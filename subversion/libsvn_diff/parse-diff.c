  svn_diff_hunk_t dummy;
      if (parse_hunk_header(line->data, &dummy, "@@", scratch_pool))
        {
          /* Line is a hunk header, reverse it. */
          line = svn_stringbuf_createf(result_pool,
                                       "@@ -%lu,%lu +%lu,%lu @@",
                                       hunk->modified_start,
                                       hunk->modified_length,
                                       hunk->original_start,
                                       hunk->original_length);
        }
      else if (parse_hunk_header(line->data, &dummy, "##", scratch_pool))
        {
          /* Line is a hunk header, reverse it. */
          line = svn_stringbuf_createf(result_pool,
                                       "## -%lu,%lu +%lu,%lu ##",
                                       hunk->modified_start,
                                       hunk->modified_length,
                                       hunk->original_start,
                                       hunk->original_length);
        }
      else
        {
          if (line->data[0] == '+')
            line->data[0] = '-';
          else if (line->data[0] == '-')
            line->data[0] = '+';
        }
svn_diff_parse_next_patch(svn_patch_t **patch,
      *patch = NULL;
  *patch = apr_pcalloc(result_pool, sizeof(**patch));
              SVN_ERR(transitions[i].fn(&state, line->data, *patch,
  (*patch)->reverse = reverse;
      temp = (*patch)->old_filename;
      (*patch)->old_filename = (*patch)->new_filename;
      (*patch)->new_filename = temp;
  if ((*patch)->old_filename == NULL || (*patch)->new_filename == NULL)
      *patch = NULL;
    SVN_ERR(parse_hunks(*patch, patch_file->apr_file, ignore_whitespace,
  if (*patch)
      qsort((*patch)->hunks->elts, (*patch)->hunks->nelts,
            (*patch)->hunks->elt_size, compare_hunks);