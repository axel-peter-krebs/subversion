#include <stddef.h>
#include "svn_hash.h"
#include "svn_ctype.h"
#include "svn_mergeinfo.h"
#include "private/svn_diff_private.h"
#include "private/svn_sorts_private.h"
svn_error_t *
svn_diff_hunk__create_adds_single_line(svn_diff_hunk_t **hunk_out,
                                       const char *line,
                                       svn_patch_t *patch,
                                       apr_pool_t *result_pool,
                                       apr_pool_t *scratch_pool)
{
  svn_diff_hunk_t *hunk = apr_palloc(result_pool, sizeof(*hunk));
  static const char hunk_header[] = "@@ -0,0 +1 @@\n";
  const unsigned len = strlen(line);
  /* The +1 is for the 'plus' start-of-line character. */
  const apr_off_t end = STRLEN_LITERAL(hunk_header) + (1 + len);
  /* The +1 is for the second \n. */
  svn_stringbuf_t *buf = svn_stringbuf_create_ensure(end + 1, scratch_pool);

  hunk->patch = patch;

  /* hunk->apr_file is created below. */

  hunk->diff_text_range.start = STRLEN_LITERAL(hunk_header);
  hunk->diff_text_range.current = STRLEN_LITERAL(hunk_header);
  hunk->diff_text_range.end = end;

  hunk->original_text_range.start = 0; /* There's no "original" text. */
  hunk->original_text_range.current = 0;
  hunk->original_text_range.end = 0;

  hunk->modified_text_range.start = STRLEN_LITERAL(hunk_header);
  hunk->modified_text_range.current = STRLEN_LITERAL(hunk_header);
  hunk->modified_text_range.end = end;

  hunk->leading_context = 0;
  hunk->trailing_context = 0;

  /* Create APR_FILE and put just a hunk in it (without a diff header).
   * Save the offset of the last byte of the diff line. */
  svn_stringbuf_appendbytes(buf, hunk_header, STRLEN_LITERAL(hunk_header));
  svn_stringbuf_appendbyte(buf, '+');
  svn_stringbuf_appendbytes(buf, line, len);
  svn_stringbuf_appendbyte(buf, '\n');

  SVN_ERR(svn_io_open_unique_file3(&hunk->apr_file, NULL /* filename */,
                                   NULL /* system tempdir */,
                                   svn_io_file_del_on_pool_cleanup,
                                   result_pool, scratch_pool));
  SVN_ERR(svn_io_file_write_full(hunk->apr_file,
                                 buf->data, buf->len,
                                 NULL, scratch_pool));
  /* No need to seek. */

  *hunk_out = hunk;
  return SVN_NO_ERROR;
}

      *stringbuf = svn_stringbuf_create_empty(result_pool);
      SVN_ERR(svn_io_file_readline(file, &str, eol, eof, max_len,
                                   result_pool, scratch_pool));
      *stringbuf = svn_stringbuf_create_empty(result_pool);
  SVN_ERR(svn_io_file_readline(hunk->apr_file, &line, eol, eof, max_len,
                               result_pool,
      if (line->data[0] == '+')
        line->data[0] = '-';
      else if (line->data[0] == '-')
        line->data[0] = '+';

/* A helper function to parse svn:mergeinfo diffs.
 *
 * These diffs use a special pretty-print format, for instance:
 *
 * Added: svn:mergeinfo
 * ## -0,0 +0,1 ##
 *   Merged /trunk:r2-3
 *
 * The hunk header has the following format:
 * ## -0,NUMBER_OF_REVERSE_MERGES +0,NUMBER_OF_FORWARD_MERGES ##
 *
 * At this point, the number of reverse merges has already been
 * parsed into HUNK->ORIGINAL_LENGTH, and the number of forward
 * merges has been parsed into HUNK->MODIFIED_LENGTH.
 *
 * The header is followed by a list of mergeinfo, one path per line.
 * This function parses such lines. Lines describing reverse merges
 * appear first, and then all lines describing forward merges appear.
 *
 * Parts of the line are affected by i18n. The words 'Merged'
 * and 'Reverse-merged' can appear in any language and at any
 * position within the line. We can only assume that a leading
 * '/' starts the merge source path, the path is followed by
 * ":r", which in turn is followed by a mergeinfo revision range,
 *  which is terminated by whitespace or end-of-string.
 *
 * If the current line meets the above criteria and we're able
 * to parse valid mergeinfo from it, the resulting mergeinfo
 * is added to patch->mergeinfo or patch->reverse_mergeinfo,
 * and we proceed to the next line.
 */
static svn_error_t *
parse_mergeinfo(svn_boolean_t *found_mergeinfo,
                svn_stringbuf_t *line,
                svn_diff_hunk_t *hunk,
                svn_patch_t *patch,
                apr_pool_t *result_pool,
                apr_pool_t *scratch_pool)
{
  char *slash = strchr(line->data, '/');
  char *colon = strrchr(line->data, ':');

  *found_mergeinfo = FALSE;

  if (slash && colon && colon[1] == 'r' && slash < colon)
    {
      svn_stringbuf_t *input;
      svn_mergeinfo_t mergeinfo = NULL;
      char *s;
      svn_error_t *err;

      input = svn_stringbuf_create_ensure(line->len, scratch_pool);

      /* Copy the merge source path + colon */
      s = slash;
      while (s <= colon)
        {
          svn_stringbuf_appendbyte(input, *s);
          s++;
        }

      /* skip 'r' after colon */
      s++;

      /* Copy the revision range. */
      while (s < line->data + line->len)
        {
          if (svn_ctype_isspace(*s))
            break;
          svn_stringbuf_appendbyte(input, *s);
          s++;
        }

      err = svn_mergeinfo_parse(&mergeinfo, input->data, result_pool);
      if (err && err->apr_err == SVN_ERR_MERGEINFO_PARSE_ERROR)
        {
          svn_error_clear(err);
          mergeinfo = NULL;
        }
      else
        SVN_ERR(err);

      if (mergeinfo)
        {
          if (hunk->original_length > 0) /* reverse merges */
            {
              if (patch->reverse)
                {
                  if (patch->mergeinfo == NULL)
                    patch->mergeinfo = mergeinfo;
                  else
                    SVN_ERR(svn_mergeinfo_merge2(patch->mergeinfo,
                                                 mergeinfo,
                                                 result_pool,
                                                 scratch_pool));
                }
              else
                {
                  if (patch->reverse_mergeinfo == NULL)
                    patch->reverse_mergeinfo = mergeinfo;
                  else
                    SVN_ERR(svn_mergeinfo_merge2(patch->reverse_mergeinfo,
                                                 mergeinfo,
                                                 result_pool,
                                                 scratch_pool));
                }
              hunk->original_length--;
            }
          else if (hunk->modified_length > 0) /* forward merges */
            {
              if (patch->reverse)
                {
                  if (patch->reverse_mergeinfo == NULL)
                    patch->reverse_mergeinfo = mergeinfo;
                  else
                    SVN_ERR(svn_mergeinfo_merge2(patch->reverse_mergeinfo,
                                                 mergeinfo,
                                                 result_pool,
                                                 scratch_pool));
                }
              else
                {
                  if (patch->mergeinfo == NULL)
                    patch->mergeinfo = mergeinfo;
                  else
                    SVN_ERR(svn_mergeinfo_merge2(patch->mergeinfo,
                                                 mergeinfo,
                                                 result_pool,
                                                 scratch_pool));
                }
              hunk->modified_length--;
            }

          *found_mergeinfo = TRUE;
        }
    }

  return SVN_NO_ERROR;
}

      SVN_ERR(svn_io_file_readline(apr_file, &line, NULL, &eof, APR_SIZE_MAX,
                                   iterpool, iterpool));
      /* Lines starting with a backslash indicate a missing EOL:
       * "\ No newline at end of file" or "end of property". */
          if (in_hunk)
      if (in_hunk && *is_property && *prop_name &&
          strcmp(*prop_name, SVN_PROP_MERGEINFO) == 0)
        {
          svn_boolean_t found_mergeinfo;

          SVN_ERR(parse_mergeinfo(&found_mergeinfo, line, *hunk, patch,
                                  result_pool, iterpool));
          if (found_mergeinfo)
            continue; /* Proceed to the next line in the patch. */
        }

   state_old_mode_seen,   /* old mode 100644 */
      ptrdiff_t len_old;
      ptrdiff_t len_new;
/* Helper for git_old_mode() and git_new_mode().  Translate the git
 * file mode MODE_STR into a binary "executable?" notion EXECUTABLE_P. */
static svn_error_t *
parse_bits_into_executability(svn_tristate_t *executable_p,
                              const char *mode_str)
{
  apr_uint64_t mode;
  SVN_ERR(svn_cstring_strtoui64(&mode, mode_str,
                                0 /* min */,
                                0777777 /* max: six octal digits */,
                                010 /* radix (octal) */));
  switch (mode & 0777)
    {
      case 0644:
        *executable_p = svn_tristate_false;
        break;

      case 0755:
        *executable_p = svn_tristate_true;
        break;

      default:
        /* Ignore unknown values. */
        *executable_p = svn_tristate_unknown;
        break;
    }

  return SVN_NO_ERROR;
}

/* Parse the 'old mode ' line of a git extended unidiff. */
static svn_error_t *
git_old_mode(enum parse_state *new_state, char *line, svn_patch_t *patch,
             apr_pool_t *result_pool, apr_pool_t *scratch_pool)
{
  SVN_ERR(parse_bits_into_executability(&patch->old_executable_p,
                                        line + STRLEN_LITERAL("old mode ")));

#ifdef SVN_DEBUG
  /* If this assert trips, the "old mode" is neither ...644 nor ...755 . */
  SVN_ERR_ASSERT(patch->old_executable_p != svn_tristate_unknown);
#endif

  *new_state = state_old_mode_seen;
  return SVN_NO_ERROR;
}

/* Parse the 'new mode ' line of a git extended unidiff. */
static svn_error_t *
git_new_mode(enum parse_state *new_state, char *line, svn_patch_t *patch,
             apr_pool_t *result_pool, apr_pool_t *scratch_pool)
{
  SVN_ERR(parse_bits_into_executability(&patch->new_executable_p,
                                        line + STRLEN_LITERAL("new mode ")));

#ifdef SVN_DEBUG
  /* If this assert trips, the "old mode" is neither ...644 nor ...755 . */
  SVN_ERR_ASSERT(patch->new_executable_p != svn_tristate_unknown);
#endif

  /* Don't touch patch->operation. */

  *new_state = state_git_tree_seen;
  return SVN_NO_ERROR;
}

  SVN_ERR(
    parse_bits_into_executability(&patch->new_executable_p,
                                  line + STRLEN_LITERAL("new file mode ")));

  SVN_ERR(
    parse_bits_into_executability(&patch->old_executable_p,
                                  line + STRLEN_LITERAL("deleted file mode ")));

  prop_patch = svn_hash_gets(patch->prop_patches, prop_name);
      svn_hash_sets(patch->prop_patches, prop_name, prop_patch);
                           APR_READ | APR_BUFFERED, APR_OS_DEFAULT,
                           result_pool));

          /* Skip svn:mergeinfo properties.
           * Mergeinfo data cannot be represented as a hunk and
           * is therefore stored in PATCH itself. */
          if (strcmp(prop_name, SVN_PROP_MERGEINFO) == 0)
            continue;



  {"old mode ",     state_git_diff_seen,    git_old_mode},
  {"new mode ",     state_old_mode_seen,    git_new_mode},




svn_diff_parse_next_patch(svn_patch_t **patch_p,
  svn_patch_t *patch;
      *patch_p = NULL;
  patch = apr_pcalloc(result_pool, sizeof(*patch));
  patch->old_executable_p = svn_tristate_unknown;
  patch->new_executable_p = svn_tristate_unknown;
      SVN_ERR(svn_io_file_readline(patch_file->apr_file, &line, NULL, &eof,
                                   APR_SIZE_MAX, iterpool, iterpool));
              SVN_ERR(transitions[i].fn(&state, line->data, patch,
               && state != state_git_diff_seen
  patch->reverse = reverse;
      temp = patch->old_filename;
      patch->old_filename = patch->new_filename;
      patch->new_filename = temp;
  if (patch->old_filename == NULL || patch->new_filename == NULL)
      patch = NULL;
    SVN_ERR(parse_hunks(patch, patch_file->apr_file, ignore_whitespace,
  if (patch)
      svn_sort__array(patch->hunks, compare_hunks);
  *patch_p = patch;