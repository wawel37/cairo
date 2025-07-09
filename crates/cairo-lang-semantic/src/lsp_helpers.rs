use std::collections::{HashSet, VecDeque};
use std::sync::Arc;

use cairo_lang_defs::ids::{
    FileIndex, GenericTypeId, ImportableId, LanguageElementId, ModuleFileId, ModuleId,
    NamedLanguageElementId, TraitFunctionId, TraitId,
};
use cairo_lang_filesystem::db::{CORELIB_CRATE_NAME, get_parent_and_mapping, translate_location};
use cairo_lang_filesystem::ids::{CodeMapping, CrateId, CrateLongId, FileId, FileLongId};
use cairo_lang_syntax::node::SyntaxNode;
use cairo_lang_syntax::node::kind::SyntaxKind;
use cairo_lang_utils::Intern;
use cairo_lang_utils::LookupIntern;
use cairo_lang_utils::ordered_hash_map::{Entry, OrderedHashMap};
use cairo_lang_utils::ordered_hash_set::OrderedHashSet;
use cairo_lang_utils::unordered_hash_set::UnorderedHashSet;
use itertools::chain;
use smol_str::SmolStr;

use crate::Variant;
use crate::corelib::{self, core_submodule, get_submodule};
use crate::db::SemanticGroup;
use crate::expr::inference::InferenceId;
use crate::items::functions::GenericFunctionId;
use crate::items::us::SemanticUseEx;
use crate::keyword::SELF_PARAM_KW;
use crate::resolve::{ResolvedGenericItem, Resolver};
use crate::types::TypeHead;

/// A filter for types.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum TypeFilter {
    /// No filter is applied.
    NoFilter,
    /// Only methods with the given type head are returned.
    TypeHead(TypeHead),
}

/// Query implementation of [crate::db::SemanticGroup::methods_in_module].
pub fn methods_in_module(
    db: &dyn SemanticGroup,
    module_id: ModuleId,
    type_filter: TypeFilter,
) -> Arc<[TraitFunctionId]> {
    let mut result = Vec::new();
    let Ok(module_traits_ids) = db.module_traits_ids(module_id) else {
        return result.into();
    };
    for trait_id in module_traits_ids.iter().copied() {
        for (_, trait_function) in db.trait_functions(trait_id).unwrap_or_default() {
            let Ok(signature) = db.trait_function_signature(trait_function) else {
                continue;
            };
            let Some(first_param) = signature.params.first() else {
                continue;
            };
            if first_param.name != SELF_PARAM_KW {
                continue;
            }
            if let TypeFilter::TypeHead(type_head) = &type_filter {
                if let Some(head) = first_param.ty.head(db) {
                    if !fit_for_method(&head, type_head) {
                        continue;
                    }
                }
            }

            result.push(trait_function)
        }
    }
    result.into()
}

/// Checks if a type head can fit for a method.
fn fit_for_method(head: &TypeHead, type_head: &TypeHead) -> bool {
    if head == type_head {
        return true;
    }
    if let TypeHead::Snapshot(snapshot_head) = head {
        return snapshot_head.as_ref() == type_head;
    }
    false
}

/// Query implementation of [crate::db::SemanticGroup::methods_in_crate].
pub fn methods_in_crate(
    db: &dyn SemanticGroup,
    crate_id: CrateId,
    type_filter: TypeFilter,
) -> Arc<[TraitFunctionId]> {
    let mut result = Vec::new();
    for module_id in db.crate_modules(crate_id).iter() {
        result.extend_from_slice(&db.methods_in_module(*module_id, type_filter.clone())[..])
    }
    result.into()
}

/// Query implementation of [crate::db::SemanticGroup::visible_importables_in_module].
pub fn visible_importables_in_module(
    db: &dyn SemanticGroup,
    module_id: ModuleId,
    user_module_file_id: ModuleFileId,
    include_parent: bool,
) -> Arc<[(ImportableId, String)]> {
    let mut visited_modules = UnorderedHashSet::default();
    visible_importables_in_module_ex(
        db,
        module_id,
        user_module_file_id,
        include_parent,
        &mut visited_modules,
    )
    .unwrap_or_else(|| Vec::new().into())
}

/// Returns the visible importables in a module, including the importables in the parent module if
/// needed. The visibility is relative to the module `user_module_id`.
fn visible_importables_in_module_ex(
    db: &dyn SemanticGroup,
    module_id: ModuleId,
    user_module_file_id: ModuleFileId,
    include_parent: bool,
    visited_modules: &mut UnorderedHashSet<ModuleId>,
) -> Option<Arc<[(ImportableId, String)]>> {
    let mut result = Vec::new();
    if visited_modules.contains(&module_id) {
        return Some(result.into());
    }

    let resolver = Resolver::new(db, user_module_file_id, InferenceId::NoContext);

    // Check if an item in the current module is visible from the user module.
    let is_visible = |item_name: SmolStr| {
        let item_info = db.module_item_info_by_name(module_id, item_name).ok()??;
        Some(resolver.is_item_visible(module_id, &item_info, user_module_file_id.0))
    };
    visited_modules.insert(module_id);
    let mut modules_to_visit = vec![];
    // Add importables and traverse modules imported into the current module.
    for use_id in db.module_uses_ids(module_id).unwrap_or_default().iter().copied() {
        if !is_visible(use_id.name(db)).unwrap_or_default() {
            continue;
        }
        let Ok(resolved_item) = db.use_resolved_item(use_id) else {
            continue;
        };
        let (resolved_item, name) = match resolved_item {
            ResolvedGenericItem::Module(ModuleId::CrateRoot(crate_id)) => {
                result.extend_from_slice(
                    &db.visible_importables_in_crate(
                        crate_id,
                        ModuleFileId(module_id, FileIndex(0)),
                    )[..],
                );

                (ImportableId::Crate(crate_id), crate_id.name(db))
            }
            ResolvedGenericItem::Module(inner_module_id @ ModuleId::Submodule(module)) => {
                modules_to_visit.push(inner_module_id);

                (ImportableId::Submodule(module), module.name(db))
            }
            ResolvedGenericItem::GenericConstant(item_id) => {
                (ImportableId::Constant(item_id), item_id.name(db))
            }
            ResolvedGenericItem::GenericFunction(GenericFunctionId::Free(item_id)) => {
                (ImportableId::FreeFunction(item_id), item_id.name(db))
            }
            ResolvedGenericItem::GenericFunction(GenericFunctionId::Extern(item_id)) => {
                (ImportableId::ExternFunction(item_id), item_id.name(db))
            }
            ResolvedGenericItem::GenericType(GenericTypeId::Struct(item_id)) => {
                (ImportableId::Struct(item_id), item_id.name(db))
            }
            ResolvedGenericItem::GenericType(GenericTypeId::Enum(item_id)) => {
                let enum_name = item_id.name(db);

                for (name, id) in db.enum_variants(item_id).unwrap_or_default() {
                    result.push((ImportableId::Variant(id), format!("{enum_name}::{name}")));
                }

                (ImportableId::Enum(item_id), enum_name)
            }
            ResolvedGenericItem::GenericType(GenericTypeId::Extern(item_id)) => {
                (ImportableId::ExternType(item_id), item_id.name(db))
            }
            ResolvedGenericItem::GenericTypeAlias(item_id) => {
                (ImportableId::TypeAlias(item_id), item_id.name(db))
            }
            ResolvedGenericItem::GenericImplAlias(item_id) => {
                (ImportableId::ImplAlias(item_id), item_id.name(db))
            }
            ResolvedGenericItem::Variant(Variant { id, .. }) => {
                (ImportableId::Variant(id), id.name(db))
            }
            ResolvedGenericItem::Trait(item_id) => (ImportableId::Trait(item_id), item_id.name(db)),
            ResolvedGenericItem::Impl(item_id) => (ImportableId::Impl(item_id), item_id.name(db)),
            ResolvedGenericItem::Macro(item_id) => {
                (ImportableId::MacroDeclaration(item_id), item_id.name(db))
            }
            ResolvedGenericItem::Variable(_)
            | ResolvedGenericItem::TraitItem(_)
            | ResolvedGenericItem::GenericFunction(GenericFunctionId::Impl(_)) => continue,
        };

        result.push((resolved_item, name.to_string()));
    }

    for submodule_id in db.module_submodules_ids(module_id).unwrap_or_default().iter().copied() {
        if !is_visible(submodule_id.name(db)).unwrap_or_default() {
            continue;
        }
        result.push((ImportableId::Submodule(submodule_id), submodule_id.name(db).to_string()));
        modules_to_visit.push(ModuleId::Submodule(submodule_id));
    }

    // Handle enums separately because we need to include their variants.
    for enum_id in db.module_enums_ids(module_id).unwrap_or_default().iter().copied() {
        let enum_name = enum_id.name(db);
        if !is_visible(enum_name.clone()).unwrap_or_default() {
            continue;
        }

        result.push((ImportableId::Enum(enum_id), enum_name.to_string()));
        for (name, id) in db.enum_variants(enum_id).unwrap_or_default() {
            result.push((ImportableId::Variant(id), format!("{enum_name}::{name}")));
        }
    }

    macro_rules! module_importables {
        ($query:ident, $map:expr) => {
            for item_id in db.$query(module_id).ok().unwrap_or_default().iter().copied() {
                if !is_visible(item_id.name(db)).unwrap_or_default() {
                    continue;
                }
                result.push(($map(item_id), item_id.name(db).to_string()));
            }
        };
    }

    module_importables!(module_constants_ids, ImportableId::Constant);
    module_importables!(module_free_functions_ids, ImportableId::FreeFunction);
    module_importables!(module_structs_ids, ImportableId::Struct);
    module_importables!(module_type_aliases_ids, ImportableId::TypeAlias);
    module_importables!(module_impl_aliases_ids, ImportableId::ImplAlias);
    module_importables!(module_traits_ids, ImportableId::Trait);
    module_importables!(module_impls_ids, ImportableId::Impl);
    module_importables!(module_extern_functions_ids, ImportableId::ExternFunction);
    module_importables!(module_extern_types_ids, ImportableId::ExternType);

    for submodule in modules_to_visit {
        for (item_id, path) in visible_importables_in_module_ex(
            db,
            submodule,
            user_module_file_id,
            false,
            visited_modules,
        )
        .unwrap_or_default()
        .iter()
        {
            result.push((*item_id, format!("{}::{}", submodule.name(db), path)));
        }
    }
    // Traverse the parent module if needed.
    if include_parent {
        match module_id {
            ModuleId::CrateRoot(_) => {}
            ModuleId::Submodule(submodule_id) => {
                let parent_module_id = submodule_id.parent_module(db);
                for (item_id, path) in visible_importables_in_module_ex(
                    db,
                    parent_module_id,
                    user_module_file_id,
                    include_parent,
                    visited_modules,
                )
                .unwrap_or_default()
                .iter()
                {
                    result.push((*item_id, format!("super::{path}")));
                }
            }
        }
    }
    Some(result.into())
}

/// Query implementation of [crate::db::SemanticGroup::visible_importables_in_crate].
pub fn visible_importables_in_crate(
    db: &dyn SemanticGroup,
    crate_id: CrateId,
    user_module_file_id: ModuleFileId,
) -> Arc<[(ImportableId, String)]> {
    let is_current_crate = user_module_file_id.0.owning_crate(db) == crate_id;
    let crate_name = if is_current_crate { "crate" } else { &crate_id.name(db) };
    let crate_as_module = ModuleId::CrateRoot(crate_id);
    db.visible_importables_in_module(crate_as_module, user_module_file_id, false)
        .iter()
        .cloned()
        .map(|(item_id, path)| (item_id, format!("{crate_name}::{path}",)))
        .collect::<Vec<_>>()
        .into()
}

/// Query implementation of [crate::db::SemanticGroup::visible_importables_from_module].
pub fn visible_importables_from_module(
    db: &dyn SemanticGroup,
    module_file_id: ModuleFileId,
) -> Option<Arc<OrderedHashMap<ImportableId, String>>> {
    let module_id = module_file_id.0;

    let current_crate_id = module_id.owning_crate(db);
    let edition = db.crate_config(current_crate_id)?.settings.edition;
    let prelude_submodule_name = edition.prelude_submodule_name();
    let core_prelude_submodule = core_submodule(db, "prelude");
    let prelude_submodule = get_submodule(db, core_prelude_submodule, prelude_submodule_name)?;
    let prelude_submodule_file_id = ModuleFileId(prelude_submodule, FileIndex(0));

    let mut module_visible_importables = Vec::new();
    // Collect importables from the prelude.
    module_visible_importables.extend_from_slice(
        &db.visible_importables_in_module(prelude_submodule, prelude_submodule_file_id, false)[..],
    );
    // Collect importables from all dependency crates, including the current crate and corelib.
    let settings = db.crate_config(current_crate_id).map(|c| c.settings).unwrap_or_default();
    for crate_id in chain!(
        [current_crate_id],
        (!settings.dependencies.contains_key(CORELIB_CRATE_NAME)).then(|| corelib::core_crate(db)),
        settings.dependencies.iter().map(|(name, setting)| {
            CrateLongId::Real {
                name: name.clone().into(),
                discriminator: setting.discriminator.clone(),
            }
            .intern(db)
        })
    ) {
        module_visible_importables
            .extend_from_slice(&db.visible_importables_in_crate(crate_id, module_file_id)[..]);
        module_visible_importables
            .push((ImportableId::Crate(crate_id), crate_id.name(db).to_string()));
    }

    // Collect importables visible in the current module.
    module_visible_importables
        .extend_from_slice(&db.visible_importables_in_module(module_id, module_file_id, true)[..]);

    // Deduplicate importables, preferring shorter paths.
    // This is the reason for searching in the crates before the current module - to prioritize
    // shorter, canonical paths prefixed with `crate::` over paths using `super::` or local
    // imports.
    let mut result: OrderedHashMap<ImportableId, String> = OrderedHashMap::default();
    for (trait_id, path) in module_visible_importables {
        match result.entry(trait_id) {
            Entry::Occupied(existing_path) => {
                if path.split("::").count() < existing_path.get().split("::").count() {
                    *existing_path.into_mut() = path;
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(path);
            }
        }
    }
    Some(result.into())
}

/// Query implementation of [crate::db::SemanticGroup::visible_traits_from_module].
pub fn visible_traits_from_module(
    db: &dyn SemanticGroup,
    module_file_id: ModuleFileId,
) -> Option<Arc<OrderedHashMap<TraitId, String>>> {
    let importables = db.visible_importables_from_module(module_file_id)?;

    let traits = importables
        .iter()
        .filter_map(|(item, path)| {
            if let ImportableId::Trait(trait_id) = item {
                Some((*trait_id, path.clone()))
            } else {
                None
            }
        })
        .collect::<OrderedHashMap<_, _>>()
        .into();

    Some(traits)
}

/// Query implemenetaion of [crate::db::SemanticGroup::node_resultants]
#[tracing::instrument(level = "trace", skip(db))]
pub fn node_resultants(db: &dyn SemanticGroup, node: SyntaxNode) -> Option<Vec<SyntaxNode>> {
    let main_file = node.stable_ptr(db).file_id(db);

    let (mut files, _) = db.file_and_subfiles_with_corresponding_modules(main_file)?;

    files.remove(&main_file);

    let files: Vec<_> = files.into_iter().collect();
    let resultants = db.find_generated_nodes(files, node);

    Some(resultants.into_iter().collect())
}

#[tracing::instrument(level = "trace", skip(db))]
pub fn file_and_subfiles_with_corresponding_modules(
    db: &dyn SemanticGroup,
    file: FileId,
) -> Option<(HashSet<FileId>, HashSet<ModuleId>)> {
    let mut modules: HashSet<_> = db.file_modules(file).ok()?.iter().copied().collect();
    let mut files = HashSet::from([file]);
    // Collect descendants of `file`
    // and modules from all virtual files that are descendants of `file`.
    //
    // Caveat: consider a situation `file1` --(child)--> `file2` with file contents:
    // - `file1`: `mod file2_origin_module { #[file2]fn sth() {} }`
    // - `file2`: `mod mod_from_file2 { }`
    //  It is important that `file2` content contains a module.
    //
    // Problem: in this situation it is not enough to call `db.file_modules(file1_id)` since
    //  `mod_from_file2` won't be in the result of this query.
    // Solution: we can find file id of `file2`
    //  (note that we only have file id of `file1` at this point)
    //  in `db.module_files(mod_from_file1_from_which_file2_origins)`.
    //  Then we can call `db.file_modules(file2_id)` to obtain module id of `mod_from_file2`.
    //  We repeat this procedure until there is nothing more to collect.
    let mut modules_queue: VecDeque<_> = modules.iter().copied().collect();
    while let Some(module_id) = modules_queue.pop_front() {
        for file_id in db.module_files(module_id).ok()?.iter() {
            if files.insert(*file_id) {
                for module_id in db.file_modules(*file_id).ok()?.iter() {
                    if modules.insert(*module_id) {
                        modules_queue.push_back(*module_id);
                    }
                }
            }
        }
    }
    Some((files, modules))
}

#[tracing::instrument(level = "trace", skip(db))]
pub fn find_generated_nodes(
    db: &dyn SemanticGroup,
    node_descendant_files: Vec<FileId>,
    node: SyntaxNode,
) -> OrderedHashSet<SyntaxNode> {
    let start_file = node.stable_ptr(db).file_id(db);

    let mut result = OrderedHashSet::default();

    let mut is_replaced = false;

    for file in node_descendant_files.iter().copied() {
        let (was_replaced, new_nodes) =
            process_file(db, node_descendant_files.clone(), start_file, node, file);
        is_replaced = is_replaced || was_replaced;
        if let Some(new_nodes) = new_nodes {
            result.extend(new_nodes);
        }
    }

    if !is_replaced {
        result.insert(node);
    }

    result
}

#[tracing::instrument(level = "trace", skip(db))]
fn process_file(
    db: &dyn SemanticGroup,
    node_descendant_files: Vec<FileId>,
    start_file: FileId,
    node: SyntaxNode,
    file: FileId,
) -> (bool, Option<OrderedHashSet<SyntaxNode>>) {
    let mut result = OrderedHashSet::default();
    let mut is_replaced = false;
    let Some((parent, mappings)) = get_parent_and_mapping(db, file) else {
        return (is_replaced, None);
    };

    if parent != start_file {
        return (is_replaced, None);
    }

    let Ok(file_syntax) = db.file_syntax(file) else {
        return (is_replaced, None);
    };

    let is_replacing_og_item = match file.lookup_intern(db) {
        FileLongId::Virtual(vfs) => vfs.original_item_removed,
        FileLongId::External(id) => db.ext_as_virtual(id).original_item_removed,
        _ => unreachable!(),
    };

    let mut new_nodes: OrderedHashSet<_> = Default::default();

    for token in file_syntax.tokens(db) {
        process_token(db, mappings.clone(), node, token).map(|new_node| new_nodes.insert(new_node));
    }

    // If there is no node found, don't mark it as potentially replaced.
    if !new_nodes.is_empty() {
        is_replaced = is_replaced || is_replacing_og_item;
    }

    for new_node in new_nodes {
        result.extend(find_generated_nodes(db, node_descendant_files.clone(), new_node));
    }

    (is_replaced, if result.is_empty() { None } else { Some(result) })
}

#[tracing::instrument(level = "trace", skip(db))]
fn process_token(
    db: &dyn SemanticGroup,
    mappings: Arc<[CodeMapping]>,
    node: SyntaxNode,
    token: SyntaxNode,
) -> Option<SyntaxNode> {
    // Skip end of the file terminal, which is also a syntax tree leaf.
    // As `ModuleItemList` and `TerminalEndOfFile` have the same parent,
    // which is the `SyntaxFile`, so we don't want to take the `SyntaxFile`
    // as an additional resultant.
    if token.kind(db) == SyntaxKind::TerminalEndOfFile {
        return None;
    }
    let nodes: Vec<_> = token
        .ancestors_with_self(db)
        .map_while(|new_node| {
            translate_location(&mappings, new_node.span(db))
                .map(|span_in_parent| (new_node, span_in_parent))
        })
        .take_while(|(_, span_in_parent)| node.span(db).contains(*span_in_parent))
        .collect();

    if let Some((last_node, _)) = nodes.last().cloned() {
        let (new_node, _) = nodes
            .into_iter()
            .rev()
            .take_while(|(node, _)| node.span(db) == last_node.span(db))
            .last()
            .unwrap();
        return Some(new_node);
        // new_nodes.insert(new_node);
    }
    None
}
