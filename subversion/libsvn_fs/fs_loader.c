/*
 * fs_loader.c:  Front-end to the various FS back ends
 *
 * ====================================================================
 * Copyright (c) 2000-2004 CollabNet.  All rights reserved.
 *
 * This software is licensed as described in the file COPYING, which
 * you should have received as part of this distribution.  The terms
 * are also available at http://subversion.tigris.org/license-1.html.
 * If newer versions of this license are posted there, you may use a
 * newer version instead, at your option.
 *
 * This software consists of voluntary contributions made by many
 * individuals.  For exact contribution history, see the revision
 * history and logs, available at http://subversion.tigris.org/.
 * ====================================================================
 */


#include "svn_fs.h"
#include "svn_private_config.h"

#include "fs.h"


svn_fs_t *
svn_fs_new (apr_hash_t *fs_config, apr_pool_t *pool)
{
}

void
svn_fs_set_warning_func (svn_fs_t *fs, svn_fs_warning_callback_t warning,
                         void *warning_baton)
{
  fs->warning = warning;
  fs->warning_baton = warning_baton;
}

svn_error_t *
svn_fs_create_berkeley (svn_fs_t *fs, const char *path)
{
}

svn_error_t *
svn_fs_open_berkeley (svn_fs_t *fs, const char *path)
{
}

const char *
svn_fs_berkeley_path (svn_fs_t *fs, apr_pool_t *pool)
{
}

svn_error_t *
svn_fs_set_berkeley_errcall (svn_fs_t *fs,
                             void (*handler) (const char *errpfx, char *msg))
{
}

svn_error_t *
svn_fs_delete_berkeley (const char *path, apr_pool_t *pool)
{
}

svn_error_t *svn_fs_hotcopy_berkeley (const char *src_path,
                                      const char *dest_path,
                                      svn_boolean_t clean_logs,
                                      apr_pool_t *pool)
{
}

svn_error_t *
svn_fs_berkeley_recover (const char *path, apr_pool_t *pool)
{
}

svn_error_t *
svn_fs_berkeley_logfiles (apr_array_header_t **logfiles,
                          const char *path,
                          svn_boolean_t only_unused,
                          apr_pool_t *pool)
{
}

int
svn_fs_compare_ids (const svn_fs_id_t *a, const svn_fs_id_t *b)
{
}

svn_boolean_t
svn_fs_check_related (const svn_fs_id_t *id1, const svn_fs_id_t *id2)
{
}

svn_fs_id_t *
svn_fs_parse_id (const char *data, apr_size_t len, apr_pool_t *pool)
{
}

svn_string_t *
svn_fs_unparse_id (const svn_fs_id_t *id, apr_pool_t *pool)
{
}

svn_error_t *
svn_fs_begin_txn (svn_fs_txn_t **txn_p, svn_fs_t *fs, svn_revnum_t rev,
                  apr_pool_t *pool)
{
  return fs->vtable->begin_txn (txn_p, fs, rev, pool);
}

svn_error_t *
svn_fs_commit_txn (const char **conflict_p, svn_revnum_t *new_rev,
                   svn_fs_txn_t *txn, apr_pool_t *pool)
{
  return txn->vtable->commit (conflict_p, new_rev, txn, pool);
}

svn_error_t *
svn_fs_abort_txn (svn_fs_txn_t *txn, apr_pool_t *pool)
{
  return txn->vtable->abort (txn, pool);
}

svn_error_t *
svn_fs_purge_txn (svn_fs_t *fs, const char *txn_id, apr_pool_t *pool)
{
  return fs->vtable->purge_txn (fs, txn_id, pool);
}

svn_error_t *
svn_fs_txn_name (const char **name_p, svn_fs_txn_t *txn, apr_pool_t *pool)
{
  *name_p = apr_pstrdup (pool, txn->name);
  return SVN_NO_ERROR;
}

svn_revnum_t
svn_fs_txn_base_revision (svn_fs_txn_t *txn)
{
  return txn->base_rev;
}

svn_error_t *
svn_fs_open_txn (svn_fs_txn_t **txn, svn_fs_t *fs, const char *name,
                 apr_pool_t *pool)
{
  return fs->vtable->open_txn (txn, fs, name, pool);
}

svn_error_t *
svn_fs_list_transactions (apr_array_header_t **names_p, svn_fs_t *fs,
                          apr_pool_t *pool)
{
  return fs->vtable->list_transactions (names_p, fs, pool);
}

svn_error_t *
svn_fs_txn_prop (svn_string_t **value_p, svn_fs_txn_t *txn,
                 const char *propname, apr_pool_t *pool)
{
  return txn->vtable->get_prop (value_p, txn, propname, pool);
}

svn_error_t *
svn_fs_txn_proplist (apr_hash_t **table_p, svn_fs_txn_t *txn, apr_pool_t *pool)
{
  return txn->vtable->get_proplist (table_p, txn, pool);
}

svn_error_t *
svn_fs_change_txn_prop (svn_fs_txn_t *txn, const char *name,
                        const svn_string_t *value, apr_pool_t *pool)
{
  return txn->vtable->change_prop (txn, name, value, pool);
}

svn_error_t *
svn_fs_revision_root (svn_fs_root_t **root_p, svn_fs_t *fs, svn_revnum_t rev,
                      apr_pool_t *pool)
{
  return fs->vtable->revision_root (root_p, fs, rev, pool);
}

svn_error_t *
svn_fs_txn_root (svn_fs_root_t **root_p, svn_fs_txn_t *txn, apr_pool_t *pool)
{
  return txn->vtable->root (root_p, txn, pool);
}

void
svn_fs_close_root (svn_fs_root_t *root)
{
  apr_pool_destroy (root->pool);
}

svn_fs_t *
svn_fs_root_fs (svn_fs_root_t *root)
{
  return root->fs;
}

svn_boolean_t
svn_fs_is_txn_root (svn_fs_root_t *root)
{
  return root->is_txn_root;
}

svn_boolean_t
svn_fs_is_revision_root (svn_fs_root_t *root)
{
  return !root->is_txn_root;
}

const char *
svn_fs_txn_root_name (svn_fs_root_t *root, apr_pool_t *pool)
{
  return root->is_txn_root ? apr_pstrdup (pool, root->txn) : NULL;
}

svn_revnum_t
svn_fs_revision_root_revision (svn_fs_root_t *root)
{
  return root->is_txn_root ? SVN_INVALID_REVNUM : root->rev;
}

svn_error_t *
svn_fs_paths_changed (apr_hash_t **changed_paths_p, svn_fs_root_t *root,
                      apr_pool_t *pool)
{
  return root->vtable->paths_changed (changed_paths_p, root, pool);
}

svn_error_t *
svn_fs_check_path (svn_node_kind_t *kind_p, svn_fs_root_t *root,
                   const char *path, apr_pool_t *pool)
{
  return root->vtable->check_path (kind_p, root, path, pool);
}

svn_error_t *
svn_fs_node_history (svn_fs_history_t **history_p, svn_fs_root_t *root,
                     const char *path, apr_pool_t *pool)
{
}

svn_error_t *
svn_fs_history_prev (svn_fs_history_t **prev_history_p,
                     svn_fs_history_t *history, svn_boolean_t cross_copies,
                     apr_pool_t *pool)
{
}

svn_error_t *
svn_fs_history_location (const char **path, svn_revnum_t *revision,
                         svn_fs_history_t *history, apr_pool_t *pool)
{
}

svn_error_t *
svn_fs_is_dir (svn_boolean_t *is_dir, svn_fs_root_t *root, const char *path,
               apr_pool_t *pool)
{
  svn_node_kind_t kind;

  SVN_ERR (root->vtable->check_path (&kind, root, path, pool));
  *is_dir = (kind == svn_node_dir);
  return SVN_NO_ERROR;
}

svn_error_t *
svn_fs_is_file (svn_boolean_t *is_file, svn_fs_root_t *root, const char *path,
                apr_pool_t *pool)
{
  svn_node_kind_t kind;

  SVN_ERR (root->vtable->check_path (&kind, root, path, pool));
  *is_file = (kind == svn_node_file);
  return SVN_NO_ERROR;
}

svn_error_t *
svn_fs_node_id (const svn_fs_id_t **id_p, svn_fs_root_t *root,
                const char *path, apr_pool_t *pool)
{
  return root->vtable->node_id (id_p, root, path, pool);
}

svn_error_t *
svn_fs_node_created_rev (svn_revnum_t *revision, svn_fs_root_t *root,
                         const char *path, apr_pool_t *pool)
{
  return root->vtable->node_created_rev (revision, root, path, pool);
}

svn_error_t *
svn_fs_node_created_path (const char **created_path, svn_fs_root_t *root,
                          const char *path, apr_pool_t *pool)
{
  return root->vtable->node_created_path (created_path, root, path, pool);
}

svn_error_t *
svn_fs_node_prop (svn_string_t **value_p, svn_fs_root_t *root,
                  const char *path, const char *propname, apr_pool_t *pool)
{
  return root->vtable->node_prop (value_p, root, path, propname, pool);
}

svn_error_t *
svn_fs_node_proplist (apr_hash_t **table_p, svn_fs_root_t *root,
                      const char *path, apr_pool_t *pool)
{
  return root->vtable->node_proplist (table_p, root, path, pool);
}

svn_error_t *
svn_fs_change_node_prop (svn_fs_root_t *root, const char *path,
                         const char *name, const svn_string_t *value,
                         apr_pool_t *pool)
{
  return root->vtable->node_prop (root, path, name, value, pool);
}

svn_error_t *
svn_fs_props_changed (svn_boolean_t *changed_p, svn_fs_root_t *root1,
                      const char *path1, svn_fs_root_t *root2,
                      const char *path2, apr_pool_t *pool)
{
  return root->vtable->props_changed (changed_p, root1, path1, root2, path2,
                                      pool);
}

svn_error_t *
svn_fs_copied_from (svn_revnum_t *rev_p, const char **path_p,
                    svn_fs_root_t *root, const char *path, apr_pool_t *pool)
{
  return root->vtable->copied_from (rev_p, path_p, root, path, pool);
}

svn_error_t *
svn_fs_merge (const char **conflict_p, svn_fs_root_t *source_root,
              const char *source_path, svn_fs_root_t *target_root,
              const char *target_path, svn_fs_root_t *ancestor_root,
              const char *ancestor_path, apr_pool_t *pool)
{
  return target_root->vtable->merge (conflict_p, source_root, source_path,
                                     target_root, target_path, ancestor_root,
                                     ancestor_path, pool);
}

svn_error_t *
svn_fs_dir_entries (apr_hash_t **entries_p, svn_fs_root_t *root,
                    const char *path, apr_pool_t *pool)
{
  return root->vtable->dir_entries (entries_p, root, path, pool);
}

svn_error_t *
svn_fs_make_dir (svn_fs_root_t *root, const char *path, apr_pool_t *pool)
{
  return root->vtable->make_dir (root, path, pool);
}

svn_error_t *
svn_fs_delete (svn_fs_root_t *root, const char *path, apr_pool_t *pool)
{
  return root->vtable->delete_node (root, path, pool);
}

svn_error_t *
svn_fs_copy (svn_fs_root_t *from_root, const char *from_path,
             svn_fs_root_t *to_root, const char *to_path, apr_pool_t *pool)
{
  return to_root->vtable->copy (from_root, from_path, to_root, to_path, pool);
}

svn_error_t *
svn_fs_revision_link (svn_fs_root_t *from_root, svn_fs_root_t *to_root,
                      const char *path, apr_pool_t *pool)
{
  return to_root->vtable->revision_link (from_root, to_root, path, pool);
}

svn_error_t *
svn_fs_file_length (svn_filesize_t *length_p, svn_fs_root_t *root,
                    const char *path, apr_pool_t *pool)
{
  return root->vtable->file_length (length_p, root, path, pool);
}

svn_error_t *
svn_fs_file_md5_checksum (unsigned char digest[], svn_fs_root_t *root,
                          const char *path, apr_pool_t *pool)
{
  return root->vtable->file_md5_checksum (digest, root, path, pool);
}

svn_error_t *
svn_fs_file_contents (svn_stream_t **contents, svn_fs_root_t *root,
                      const char *path, apr_pool_t *pool)
{
  return root->vtable->file_contents (contents, root, path, pool);
}

svn_error_t *
svn_fs_make_file (svn_fs_root_t *root, const char *path, apr_pool_t *pool)
{
  return root->vtable->make_file (root, path, pool);
}

svn_error_t *
svn_fs_apply_textdelta (svn_txdelta_window_handler_t *contents_p,
                        void **contents_baton_p, svn_fs_root_t *root,
                        const char *path, const char *base_checksum,
                        const char *result_checksum, apr_pool_t *pool)
{
  return root->vtable->apply_textdelta (contents_p, contents_baton_p, root,
                                        path, base_checksum, result_checksum,
                                        pool);
}

svn_error_t *
svn_fs_apply_text (svn_stream_t **contents_p, svn_fs_root_t *root,
                   const char *path, const char *result_checksum,
                   apr_pool_t *pool)
{
  return root->vtable->apply_text (contents_p, root, path, result_checksum,
                                   pool);
}

svn_error_t *
svn_fs_contents_changed (svn_boolean_t *changed_p, svn_fs_root_t *root1,
                         const char *path1, svn_fs_root_t *root2,
                         const char *path2, apr_pool_t *pool)
{
  return root1->vtable->contents_changed (changed_p, root1, path1, root2,
                                          path2, pool);
}

svn_error_t *
svn_fs_youngest_rev (svn_revnum_t *youngest_p, svn_fs_t *fs, apr_pool_t *pool)
{
  return fs->vtable->youngest_rev (youngest_p, fs, pool);
}

svn_error_t *
svn_fs_deltify_revision (svn_fs_t *fs, svn_revnum_t revision, apr_pool_t *pool)
{
  return fs->vtable->deltify (fs, revision, pool);
}

svn_error_t *
svn_fs_revision_prop (svn_string_t **value_p, svn_fs_t *fs, svn_revnum_t rev,
                      const char *propname, apr_pool_t *pool)
{
  return fs->vtable->revision_prop (value_p, fs, rev, propname, pool);
}

svn_error_t *
svn_fs_revision_proplist (apr_hash_t **table_p, svn_fs_t *fs, svn_revnum_t rev,
                          apr_pool_t *pool)
{
  return fs->vtable->revision_proplist (table_p, fs, rev, pool);
}

svn_error_t *
svn_fs_change_rev_prop (svn_fs_t *fs, svn_revnum_t rev, const char *name,
                        const svn_string_t *value, apr_pool_t *pool)
{
  return fs->vtable->change_rev_prop (fs, rev, name, value, pool);
}

svn_error_t *
svn_fs_get_file_delta_stream (svn_txdelta_stream_t **stream_p,
                              svn_fs_root_t *source_root,
                              const char *source_path,
                              svn_fs_root_t *target_root,
                              const char *target_path, apr_pool_t *pool)
{
  return target_root->vtable->get_file_delta_stream (stream_p, source_root,
                                                     source_path, target_root,
                                                     target_path, pool);
}

svn_error_t *
svn_fs_get_uuid (svn_fs_t *fs, const char **uuid, apr_pool_t *pool)
{
  return fs->vtable->get_uuid (fs, uuid, pool);
}

svn_error_t *
svn_fs_set_uuid (svn_fs_t *fs, const char *uuid, apr_pool_t *pool)
{
  return fs->vtable->set_uuid (fs, uuid, pool);
}
