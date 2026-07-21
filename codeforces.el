;;; codeforces.el --- Codeforces client -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2026 Luke Holland
;;
;; Author: Luke Holland
;; Maintainer: Luke Holland
;; Created: June 11, 2026
;; Modified: June 11, 2026
;; Version: 0.1.0
;; Keywords: tools
;; Homepage: https://github.com/yelobat/codeforces.el
;; Package-Requires: ((emacs "28.1"))
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;; # Overview
;;
;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'seq)
(require 'url)
(require 'url-util)
(require 'dom)
(require 'format-spec)
(require 'tabulated-list)
(require 'transient)

(defvar json-array-type)
(defvar json-object-type)
(defvar json-false)
(defvar json-null)
(declare-function json-read "json")

;;;; Customization

(defgroup codeforces nil
  "Codeforces client and practice environment."
  :group 'tools
  :prefix "codeforces-")

(defcustom codeforces-handle nil
  "Your Codeforces handle.
Used for the \"unsolved only\" filter, submission history, and the
user info commands."
  :type '(choice (const :tag "Unset" nil) string))

(defcustom codeforces-api-key nil
  "Codeforces API key.
Generate one at URL `https://codeforces.com/settings/api'.  Only
required for authenticated methods such as `user.friends'."
  :type '(choice (const :tag "Unset" nil) string))

(defcustom codeforces-api-secret nil
  "Codeforces API secret matching `codeforces-api-key'."
  :type '(choice (const :tag "Unset" nil) string))

(defcustom codeforces-directory (expand-file-name "~/codeforces")
  "Directory under which per-problem workspaces are created."
  :type 'directory)

(defcustom codeforces-default-language "rust"
  "Default language key (a car of `codeforces-languages').
If nil, `codeforces-start-problem' prompts every time."
  :type '(choice (const :tag "Always prompt" nil) string))

(defcustom codeforces-rate-limit 2.1
  "Minimum number of seconds between API requests.
The Codeforces API permits at most one request per two seconds."
  :type 'number)

(defcustom codeforces-request-timeout 30
  "Timeout in seconds for HTTP requests."
  :type 'integer)

(defcustom codeforces-test-timeout 10
  "Per-test wall-clock limit in seconds for the local test runner."
  :type 'integer)

(defcustom codeforces-timeout-program "timeout"
  "Program used to enforce `codeforces-test-timeout'.
Set to nil to run tests without a time limit."
  :type '(choice (const :tag "No limit" nil) string))

(defcustom codeforces-open-function #'browse-url
  "Function used to open Codeforces URLs (e.g. `browse-url' or `eww')."
  :type 'function)

(defcustom codeforces-binary-name "cf-bin"
  "Base name for compiled artifacts inside a workspace (the %b spec)."
  :type 'string)

(defcustom codeforces-standings-count 50
  "How many rows to fetch for `codeforces-standings'."
  :type 'integer)

(defcustom codeforces-submissions-count 50
  "How many submissions to fetch for `codeforces-my-submissions'."
  :type 'integer)

(defcustom codeforces-user-agent
  "Mozilla/5.0 (X11; Linux x86_64) codeforces.el (Emacs)"
  "User-Agent header sent with HTTP requests."
  :type 'string)

;;;; Languages
;;
;; Each entry is (KEY . PLIST) with:
;;   :extension      file extension (no dot)
;;   :filename       solution file name (default "sol.EXTENSION";
;;                   languages like Java need a fixed name)
;;   :compile        shell command, or nil for interpreted languages
;;   :run            shell command producing output on stdout
;;   :template-file  template file in `codeforces-template-directory'
;;                   (default "KEY.EXTENSION")
;;   :template       literal template string; overrides :template-file
;;   :extra-files    alist of (FILENAME . CONTENT) also written into a
;;                   new workspace, for languages whose tooling needs a
;;                   project file
;;
;; Commands are run with the workspace as `default-directory' and
;; support `format-spec' escapes:
;;   %f  solution file (shell-quoted)
;;   %b  binary path, `codeforces-binary-name' in the workspace
;;   %d  workspace directory
;;
;; Any language Codeforces accepts can be added here.

(defconst codeforces--library-directory
  (let ((file (or load-file-name buffer-file-name default-directory)))
    (file-name-directory
     (file-truename (concat (file-name-sans-extension file) ".el"))))
  "Directory containing codeforces.el, used to locate bundled templates.")

(defcustom codeforces-template-directory nil
  "Directory containing per-language solution templates."
  :type '(choice (const :tag "Bundled templates" nil) directory))

(defcustom codeforces-languages
  '(("cpp"
     :extension "cpp"
     :compile "g++ -std=c++17 -O2 -Wall -o %b %f"
     :run "%b")
    ("rust"
     :extension "rs"
     :compile "rustc --edition 2021 -O -o %b %f"
     :run "%b"
     :extra-files (("Cargo.toml" . "[package]\nname = \"sol\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[[bin]]\nname = \"sol\"\npath = \"sol.rs\"\n\n[workspace]\n")
                   (".gitignore" . "/target\n"))))
  "Alist mapping a language key to a configuration plist.
See the comment above this variable for the plist keys and the
`format-spec' escapes supported in :compile and :run."
  :type '(alist :key-type string :value-type plist))

(defcustom codeforces-mode-line-lighter " CF"
  "Mode line lighter for `codeforces-mode'."
  :type 'string)

;;;; Internal state

(defvar codeforces--last-request-time 0.0
  "Time of the most recent API request, as a float.")

(defvar codeforces--problems-cache nil
  "Cached list of problem alists from `problemset.problems'.")

(defvar codeforces--tags-cache nil
  "Cached list of all known problem tags.")

(defvar codeforces--solved-cache nil
  "Hash table of \"contestId/index\" keys the user has solved.")

(defvar codeforces--rng-seeded nil
  "Non-nil once the random number generator has been seeded.")

;; Filters used by the random picker and the problem browser.
(defvar codeforces-filter-min-rating nil
  "Minimum problem rating filter, or nil.")
(defvar codeforces-filter-max-rating nil
  "Maximum problem rating filter, or nil.")
(defvar codeforces-filter-tags nil
  "List of tags a problem must have, or nil.")
(defvar codeforces-filter-unsolved-only nil
  "When non-nil, filter out problems `codeforces-handle' has solved.")

;;;; HTTP / JSON plumbing

(define-error 'codeforces-error "Codeforces error")

(defun codeforces--parse-json ()
  "Parse the JSON object following point in the current buffer."
  (if (fboundp 'json-parse-buffer)
      (json-parse-buffer :object-type 'alist
                         :array-type 'list
                         :false-object nil
                         :null-object nil)
    (require 'json)
    (let ((json-object-type 'alist)
          (json-array-type 'list)
          (json-false nil)
          (json-null nil))
      (json-read))))

(defun codeforces--throttle ()
  "Sleep long enough to respect `codeforces-rate-limit'."
  (let ((wait (- (+ codeforces--last-request-time codeforces-rate-limit)
                 (float-time))))
    (when (> wait 0)
      (sleep-for wait)))
  (setq codeforces--last-request-time (float-time)))

(defun codeforces--http-get (url)
  "Fetch URL synchronously and return the decoded body as a string."
  (let ((url-request-extra-headers
         `(("User-Agent" . ,codeforces-user-agent))))
    (let ((buffer (url-retrieve-synchronously url t t codeforces-request-timeout)))
      (unless buffer
        (signal 'codeforces-error (list (format "No response from %s" url))))
      (with-current-buffer buffer
        (unwind-protect
            (progn
              (goto-char (point-min))
              (unless (re-search-forward "^\r?\n" nil t)
                (signal 'codeforces-error (list "Malformed HTTP response")))
              (decode-coding-string
               (buffer-substring-no-properties (point) (point-max))
               'utf-8))
          (kill-buffer buffer))))))

(defun codeforces--param-value (value)
  "Render VALUE as an API parameter string.
Booleans become \"true\", lists are joined with semicolons."
  (cond ((eq value t) "true")
        ((stringp value) value)
        ((numberp value) (number-to-string value))
        ((listp value) (mapconcat (lambda (x) (format "%s" x)) value ";"))
        (t (format "%s" value))))

(defun codeforces--clean-params (params)
  "Drop nil-valued PARAMS and stringify keys and values."
  (let (out)
    (dolist (p params (nreverse out))
      (when (cdr p)
        (push (cons (format "%s" (car p))
                    (codeforces--param-value (cdr p)))
              out)))))

(defun codeforces--authenticated-p ()
  "Return non-nil when an API key and secret are configured."
  (and codeforces-api-key codeforces-api-secret t))

(defun codeforces--signed-params (method params)
  "Return PARAMS for METHOD extended with apiKey, time, and apiSig.
Implements the signing scheme from the Codeforces API documentation:
apiSig is a random prefix followed by
sha512Hex(rand /method?sortedParams#secret)."
  (let* ((rand (format "%06x" (random #x1000000)))
         (params (append params
                         `(("apiKey" . ,codeforces-api-key)
                           ("time" . ,(number-to-string (floor (float-time)))))))
         (sorted (sort (copy-sequence params)
                       (lambda (a b)
                         (string< (concat (car a) "=" (cdr a))
                                  (concat (car b) "=" (cdr b))))))
         (qs (mapconcat (lambda (p) (concat (car p) "=" (cdr p))) sorted "&"))
         (hash (secure-hash 'sha512
                            (concat rand "/" method "?" qs "#"
                                    codeforces-api-secret))))
    (append params `(("apiSig" . ,(concat rand hash))))))

(defun codeforces--query-string (params)
  "URL-encode PARAMS into a query string."
  (mapconcat (lambda (p)
               (concat (url-hexify-string (car p))
                       "="
                       (url-hexify-string (cdr p))))
             params "&"))

(defun codeforces--request (method &optional params auth)
  "Call API METHOD with PARAMS (an alist) and return its result.
PARAMS values may be strings, numbers, t, or lists (joined with
semicolons); nil values are dropped.  When AUTH is non-nil the method
requires authentication.  Requests are signed whenever credentials
are configured.  Signals `codeforces-error' on failure."
  (let ((params (codeforces--clean-params params)))
    (when auth
      (unless (codeforces--authenticated-p)
        (user-error
         "Method %s requires `codeforces-api-key' and `codeforces-api-secret'"
         method)))
    (when (codeforces--authenticated-p)
      (setq params (codeforces--signed-params method params)))
    (codeforces--throttle)
    (let* ((url (concat "https://codeforces.com/api/" method
                        (and params
                             (concat "?" (codeforces--query-string params)))))
           (body (codeforces--http-get url))
           (json (with-temp-buffer
                   (insert body)
                   (goto-char (point-min))
                   (condition-case nil
                       (codeforces--parse-json)
                     (error
                      (signal 'codeforces-error
                              (list (format "Non-JSON response from %s" method))))))))
      (if (equal (alist-get 'status json) "OK")
          (alist-get 'result json)
        (signal 'codeforces-error
                (list (format "%s: %s" method
                              (or (alist-get 'comment json) "unknown error"))))))))

(defun codeforces-api-blog-entry-comments (blog-entry-id)
  "Return comments on blog entry BLOG-ENTRY-ID (blogEntry.comments)."
  (codeforces--request "blogEntry.comments"
                       `(("blogEntryId" . ,blog-entry-id))))

(defun codeforces-api-blog-entry-view (blog-entry-id)
  "Return blog entry BLOG-ENTRY-ID in full (blogEntry.view)."
  (codeforces--request "blogEntry.view"
                       `(("blogEntryId" . ,blog-entry-id))))

(defun codeforces-api-contest-hacks (contest-id &optional as-manager)
  "Return hacks in contest CONTEST-ID (contest.hacks).
AS-MANAGER requires authentication and contest manager rights."
  (codeforces--request "contest.hacks"
                       `(("contestId" . ,contest-id)
                         ("asManager" . ,as-manager))
                       as-manager))

(defun codeforces-api-contest-list (&optional gym)
  "Return information about all contests (contest.list).
With non-nil GYM, return gym contests instead."
  (codeforces--request "contest.list" `(("gym" . ,gym))))

(defun codeforces-api-contest-rating-changes (contest-id)
  "Return rating changes after contest CONTEST-ID (contest.ratingChanges)."
  (codeforces--request "contest.ratingChanges"
                       `(("contestId" . ,contest-id))))

(cl-defun codeforces-api-contest-standings
    (contest-id &key as-manager from count handles room show-unofficial)
  "Return standings of contest CONTEST-ID (contest.standings).
FROM and COUNT select a 1-based row range; HANDLES is a list of
handles to restrict to; ROOM restricts to a room; SHOW-UNOFFICIAL
includes virtual and out-of-competition participants.  AS-MANAGER
requires authentication."
  (codeforces--request "contest.standings"
                       `(("contestId" . ,contest-id)
                         ("asManager" . ,as-manager)
                         ("from" . ,from)
                         ("count" . ,count)
                         ("handles" . ,handles)
                         ("room" . ,room)
                         ("showUnofficial" . ,show-unofficial))
                       as-manager))

(cl-defun codeforces-api-contest-status
    (contest-id &key as-manager handle from count)
  "Return submissions in contest CONTEST-ID (contest.status).
Optionally restrict to HANDLE and to a FROM/COUNT range."
  (codeforces--request "contest.status"
                       `(("contestId" . ,contest-id)
                         ("asManager" . ,as-manager)
                         ("handle" . ,handle)
                         ("from" . ,from)
                         ("count" . ,count))
                       as-manager))

(defun codeforces-api-problemset-problems (&optional tags problemset-name)
  "Return all problems, optionally filtered by TAGS (problemset.problems).
TAGS is a list of tag strings; PROBLEMSET-NAME selects an alternative
problemset such as \"acmsguru\".  The result alist has `problems' and
`problemStatistics' keys."
  (codeforces--request "problemset.problems"
                       `(("tags" . ,tags)
                         ("problemsetName" . ,problemset-name))))

(defun codeforces-api-problemset-recent-status (count &optional problemset-name)
  "Return the COUNT most recent submissions (problemset.recentStatus).
COUNT may be at most 1000.  PROBLEMSET-NAME is as in
`codeforces-api-problemset-problems'."
  (codeforces--request "problemset.recentStatus"
                       `(("count" . ,count)
                         ("problemsetName" . ,problemset-name))))

(defun codeforces-api-recent-actions (max-count)
  "Return the MAX-COUNT most recent actions (recentActions).
MAX-COUNT may be at most 100."
  (codeforces--request "recentActions" `(("maxCount" . ,max-count))))

(defun codeforces-api-user-blog-entries (handle)
  "Return blog entries by HANDLE (user.blogEntries)."
  (codeforces--request "user.blogEntries" `(("handle" . ,handle))))

(defun codeforces-api-user-friends (&optional only-online)
  "Return the authenticated user's friends (user.friends).
With non-nil ONLY-ONLINE, return only friends currently online.
Requires `codeforces-api-key' and `codeforces-api-secret'."
  (codeforces--request "user.friends"
                       `(("onlyOnline" . ,only-online))
                       t))

(defun codeforces-api-user-info (handles &optional check-historic-handles)
  "Return info about HANDLES, a handle string or list of them (user.info).
With non-nil CHECK-HISTORIC-HANDLES, renamed handles are resolved."
  (codeforces--request "user.info"
                       `(("handles" . ,(if (listp handles)
                                           handles
                                         (list handles)))
                         ("checkHistoricHandles" . ,check-historic-handles))))

(cl-defun codeforces-api-user-rated-list
    (&key active-only include-retired contest-id)
  "Return the list of rated users (user.ratedList).
ACTIVE-ONLY restricts to users active in the last month;
INCLUDE-RETIRED includes long-inactive users; CONTEST-ID restricts to
participants of that contest."
  (codeforces--request "user.ratedList"
                       `(("activeOnly" . ,active-only)
                         ("includeRetired" . ,include-retired)
                         ("contestId" . ,contest-id))))

(defun codeforces-api-user-rating (handle)
  "Return the rating history of HANDLE (user.rating)."
  (codeforces--request "user.rating" `(("handle" . ,handle))))

(defun codeforces-api-user-status (handle &optional from count)
  "Return submissions of HANDLE (user.status).
FROM is the 1-based index of the first submission to return and COUNT
the number of submissions; omit both for the full history."
  (codeforces--request "user.status"
                       `(("handle" . ,handle)
                         ("from" . ,from)
                         ("count" . ,count))))

(defun codeforces--problem-key (problem)
  "Return the \"contestId/index\" key identifying PROBLEM."
  (format "%s/%s"
          (alist-get 'contestId problem)
          (alist-get 'index problem)))

(defun codeforces--problem-id (problem)
  "Return the short ID of PROBLEM, e.g. \"1700A\"."
  (format "%s%s"
          (or (alist-get 'contestId problem) "?")
          (alist-get 'index problem)))

(defun codeforces-problems (&optional refresh)
  "Return the cached list of all problems, fetching when needed.
With non-nil REFRESH, refetch from the API.  Each problem alist is
augmented with a `solvedCount' entry from the problem statistics."
  (when (or refresh (null codeforces--problems-cache))
    (message "codeforces: fetching problemset...")
    (let* ((result (codeforces-api-problemset-problems))
           (problems (alist-get 'problems result))
           (stats (alist-get 'problemStatistics result))
           (counts (make-hash-table :test #'equal))
           (tags (make-hash-table :test #'equal)))
      (dolist (s stats)
        (puthash (codeforces--problem-key s)
                 (alist-get 'solvedCount s)
                 counts))
      (setq codeforces--problems-cache
            (mapcar (lambda (p)
                      (dolist (tag (alist-get 'tags p))
                        (puthash tag t tags))
                      (cons (cons 'solvedCount
                                  (gethash (codeforces--problem-key p) counts))
                            p))
                    problems))
      (setq codeforces--tags-cache
            (sort (hash-table-keys tags) #'string<))
      (message "codeforces: %d problems cached"
               (length codeforces--problems-cache))))
  codeforces--problems-cache)

(defun codeforces-all-tags ()
  "Return the sorted list of all known problem tags."
  (codeforces-problems)
  codeforces--tags-cache)

(defun codeforces-solved-set (&optional refresh)
  "Return a hash table of problem keys solved by `codeforces-handle'.
Returns nil when no handle is configured.  With non-nil REFRESH,
refetch the submission history."
  (when codeforces-handle
    (when (or refresh (null codeforces--solved-cache))
      (message "codeforces: fetching submissions for %s..." codeforces-handle)
      (let ((submissions (codeforces-api-user-status codeforces-handle))
            (table (make-hash-table :test #'equal)))
        (dolist (sub submissions)
          (when (equal (alist-get 'verdict sub) "OK")
            (puthash (codeforces--problem-key (alist-get 'problem sub))
                     t table)))
        (setq codeforces--solved-cache table)))
    codeforces--solved-cache))

(defun codeforces-refresh ()
  "Drop and refetch the problem and solved-submission caches."
  (interactive)
  (setq codeforces--problems-cache nil
        codeforces--tags-cache nil
        codeforces--solved-cache nil)
  (codeforces-problems t)
  (when codeforces-handle
    (codeforces-solved-set t))
  (message "codeforces: caches refreshed"))

(defun codeforces--problem-matches-p (problem solved)
  "Return non-nil when PROBLEM passes the current filters.
SOLVED is the hash table from `codeforces-solved-set' or nil."
  (let ((rating (alist-get 'rating problem))
        (tags (alist-get 'tags problem)))
    (and (or (null codeforces-filter-min-rating)
             (and rating (>= rating codeforces-filter-min-rating)))
         (or (null codeforces-filter-max-rating)
             (and rating (<= rating codeforces-filter-max-rating)))
         (or (null codeforces-filter-tags)
             (cl-subsetp codeforces-filter-tags tags :test #'string=))
         (or (not codeforces-filter-unsolved-only)
             (null solved)
             (not (gethash (codeforces--problem-key problem) solved))))))

(defun codeforces-filtered-problems ()
  "Return all problems matching the current filters."
  (let ((solved (and codeforces-filter-unsolved-only
                     (codeforces-solved-set))))
    (cl-remove-if-not (lambda (p) (codeforces--problem-matches-p p solved))
                      (codeforces-problems))))

(defun codeforces--filter-description ()
  "Return a one-line human-readable description of the current filters."
  (let (parts)
    (when (or codeforces-filter-min-rating codeforces-filter-max-rating)
      (push (format "rating %s..%s"
                    (or codeforces-filter-min-rating "*")
                    (or codeforces-filter-max-rating "*"))
            parts))
    (when codeforces-filter-tags
      (push (format "tags: %s" (string-join codeforces-filter-tags ", "))
            parts))
    (when codeforces-filter-unsolved-only
      (push "unsolved only" parts))
    (if parts
        (string-join (nreverse parts) "; ")
      "no filters")))

;;;###autoload
(defun codeforces-set-filters ()
  "Interactively set the rating, tag, and solved-status filters."
  (interactive)
  (let ((min (read-string "Min rating (empty for none): "
                          (and codeforces-filter-min-rating
                               (number-to-string codeforces-filter-min-rating))))
        (max (read-string "Max rating (empty for none): "
                          (and codeforces-filter-max-rating
                               (number-to-string codeforces-filter-max-rating)))))
    (setq codeforces-filter-min-rating
          (unless (string-empty-p (string-trim min))
            (string-to-number min)))
    (setq codeforces-filter-max-rating
          (unless (string-empty-p (string-trim max))
            (string-to-number max)))
    (setq codeforces-filter-tags
          (completing-read-multiple "Tags (comma-separated, empty for any): "
                                    (codeforces-all-tags)
                                    nil nil
                                    (string-join codeforces-filter-tags ",")))
    (setq codeforces-filter-unsolved-only
          (and codeforces-handle
               (y-or-n-p (format "Only problems %s has not solved? "
                                 codeforces-handle))))
    (message "codeforces: %s" (codeforces--filter-description))))

;;;###autoload
(defun codeforces-clear-filters ()
  "Reset all problem filters."
  (interactive)
  (setq codeforces-filter-min-rating nil
        codeforces-filter-max-rating nil
        codeforces-filter-tags nil
        codeforces-filter-unsolved-only nil)
  (message "codeforces: filters cleared"))

(defun codeforces--random-elt (list)
  "Return a uniformly random element of LIST."
  (unless codeforces--rng-seeded
    (random t)
    (setq codeforces--rng-seeded t))
  (nth (random (length list)) list))

(defun codeforces--describe-problem (problem)
  "Return a one-line description of PROBLEM."
  (format "%s — %s  (rating %s, solved %s)  [%s]"
          (codeforces--problem-id problem)
          (alist-get 'name problem)
          (or (alist-get 'rating problem) "?")
          (or (alist-get 'solvedCount problem) "?")
          (string-join (alist-get 'tags problem) ", ")))

;;;###autoload
(defun codeforces-random-problem (&optional set-filters)
  "Pick a random problem matching the current filters and offer to start.
With prefix argument SET-FILTERS, prompt for filters first."
  (interactive "P")
  (when set-filters
    (codeforces-set-filters))
  (let ((candidates (codeforces-filtered-problems)))
    (unless candidates
      (user-error "No problems match the current filters (%s)"
                  (codeforces--filter-description)))
    (let ((problem (codeforces--random-elt candidates)))
      (if (y-or-n-p (format "%s — start solving? "
                            (codeforces--describe-problem problem)))
          (codeforces-start-problem problem)
        (message "%s" (codeforces--describe-problem problem))))))

;;;###autoload
(defun codeforces-roll (&optional set-filters)
  "Pick a random filtered problem and start a workspace immediately.
With prefix argument SET-FILTERS, prompt for filters first."
  (interactive "P")
  (when set-filters
    (codeforces-set-filters))
  (let ((candidates (codeforces-filtered-problems)))
    (unless candidates
      (user-error "No problems match the current filters (%s)"
                  (codeforces--filter-description)))
    (codeforces-start-problem (codeforces--random-elt candidates))))

(defun codeforces--problem-url (contest-id index)
  "Return the statement URL for problem INDEX of CONTEST-ID."
  (if (and contest-id (>= contest-id 100000))
      (format "https://codeforces.com/gym/%s/problem/%s" contest-id index)
    (format "https://codeforces.com/problemset/problem/%s/%s"
            contest-id index)))

(defun codeforces--submit-url (contest-id index)
  "Return the submit-page URL for problem INDEX of CONTEST-ID."
  (if (and contest-id (>= contest-id 100000))
      (format "https://codeforces.com/gym/%s/submit" contest-id)
    (format "https://codeforces.com/contest/%s/submit/%s" contest-id index)))

(defun codeforces--decode-entities (string)
  "Decode the HTML entities Codeforces uses in sample blocks in STRING."
  (dolist (pair '(("&lt;" . "<") ("&gt;" . ">") ("&quot;" . "\"")
                  ("&#39;" . "'") ("&apos;" . "'") ("&nbsp;" . " ")
                  ("&amp;" . "&")))
    (setq string (replace-regexp-in-string
                  (regexp-quote (car pair)) (cdr pair) string t t)))
  string)

(defun codeforces--clean-sample (string)
  "Normalize line endings and surrounding whitespace in sample STRING."
  (let ((s (replace-regexp-in-string "\r" "" string)))
    (concat (string-trim s) "\n")))

(defun codeforces--dom-pre-text (node)
  "Extract the text of a sample <pre> DOM NODE.
<br> becomes a newline; per-line <div> wrappers (the
\"test-example-line\" markup on newer problems) are terminated with a
newline."
  (cond
   ((stringp node) node)
   ((not (consp node)) "")
   ((eq (dom-tag node) 'br) "\n")
   ((eq (dom-tag node) 'div)
    (concat (mapconcat #'codeforces--dom-pre-text (dom-children node) "")
            "\n"))
   (t (mapconcat #'codeforces--dom-pre-text (dom-children node) ""))))

(defun codeforces--extract-pre-blocks-dom (html class)
  "Extract sample <pre> texts inside divs of CLASS from HTML using libxml."
  (with-temp-buffer
    (insert html)
    (let ((dom (libxml-parse-html-region (point-min) (point-max))))
      (delq nil
            (mapcar (lambda (div)
                      (when-let* ((pre (car (dom-by-tag div 'pre))))
                        (codeforces--clean-sample
                         (codeforces--dom-pre-text pre))))
                    (dom-by-class dom (concat "\\`" class "\\'")))))))

(defun codeforces--clean-html-fragment (fragment)
  "Convert a raw sample <pre> HTML FRAGMENT into plain text."
  (let ((s fragment))
    (setq s (replace-regexp-in-string "<br[^>]*>" "\n" s t t))
    (setq s (replace-regexp-in-string "</div>" "\n" s t t))
    (setq s (replace-regexp-in-string "<[^>]+>" "" s t t))
    (codeforces--clean-sample (codeforces--decode-entities s))))

(defun codeforces--extract-pre-blocks-regexp (html class)
  "Extract sample <pre> texts inside divs of CLASS from HTML with regexps."
  (with-temp-buffer
    (insert html)
    (goto-char (point-min))
    (let ((case-fold-search t)
          blocks)
      (while (re-search-forward
              (format "<div[^>]*class=\"%s\"[^>]*>" (regexp-quote class))
              nil t)
        (when (re-search-forward "<pre[^>]*>" nil t)
          (let ((start (point)))
            (when (re-search-forward "</pre>" nil t)
              (push (codeforces--clean-html-fragment
                     (buffer-substring-no-properties
                      start (match-beginning 0)))
                    blocks)))))
      (nreverse blocks))))

(defun codeforces--extract-pre-blocks (html class)
  "Extract sample <pre> texts inside divs of CLASS from HTML."
  (if (fboundp 'libxml-parse-html-region)
      (codeforces--extract-pre-blocks-dom html class)
    (codeforces--extract-pre-blocks-regexp html class)))

(defun codeforces--parse-samples (html)
  "Return a list of (INPUT . EXPECTED-OUTPUT) sample pairs from HTML."
  (let ((inputs (codeforces--extract-pre-blocks html "input"))
        (outputs (codeforces--extract-pre-blocks html "output")))
    (cl-mapcar #'cons inputs outputs)))

(defun codeforces-fetch-samples (&optional directory html)
  "Scrape sample tests for the workspace at DIRECTORY into tests/N.{in,ans}.
DIRECTORY defaults to the current workspace.  With non-nil HTML, parse
that instead of downloading the statement again.  Existing sample files
are overwritten; tests you added by hand with higher numbers are left
alone."
  (interactive)
  (let* ((root (or directory (codeforces--workspace-root)))
         (meta (codeforces--read-metadata root))
         (url (codeforces--problem-url (plist-get meta :contest-id)
                                       (plist-get meta :index)))
         (html (or html (codeforces--http-get url)))
         (samples (codeforces--parse-samples html))
         (tests-dir (expand-file-name "tests" root))
         (n 0))
    (unless samples
      (user-error
       "No samples found at %s (layout change or anti-bot page); try `codeforces-add-test'"
       url))
    (make-directory tests-dir t)
    (dolist (sample samples)
      (setq n (1+ n))
      (write-region (car sample) nil
                    (expand-file-name (format "%d.in" n) tests-dir)
                    nil 'silent)
      (write-region (cdr sample) nil
                    (expand-file-name (format "%d.ans" n) tests-dir)
                    nil 'silent))
    (message "codeforces: wrote %d sample test(s) to %s" n tests-dir)
    n))

(defun codeforces--abs-url (href)
  "Return HREF as an absolute codeforces.com URL."
  (cond ((string-match-p "\\`https?:" href) href)
        ((string-prefix-p "/" href) (concat "https://codeforces.com" href))
        (t (concat "https://codeforces.com/" href))))

(defun codeforces--org-emph (marker s)
  "Wrap the trimmed string S in Org emphasis MARKER, or \"\" when empty."
  (let ((s (string-trim s)))
    (if (string-empty-p s) "" (concat marker s marker))))

(defun codeforces--org-inline (node)
  "Render inline DOM NODE content to an Org string."
  (cond
   ((stringp node) node)
   ((not (consp node)) "")
   (t (let ((tag (dom-tag node))
            (class (or (dom-attr node 'class) "")))
        (cond
         ((eq tag 'br) "\n")
         ((memq tag '(i em)) (codeforces--org-emph "/" (codeforces--org-children node)))
         ((memq tag '(b strong)) (codeforces--org-emph "*" (codeforces--org-children node)))
         ((eq tag 'sub) (format "_{%s}" (string-trim (dom-texts node ""))))
         ((eq tag 'sup) (format "^{%s}" (string-trim (dom-texts node ""))))
         ((eq tag 'code) (codeforces--org-emph "~" (dom-texts node "")))
         ((eq tag 'img) (let ((src (dom-attr node 'src)))
                          (if src (format "[[%s]]" (codeforces--abs-url src)) "")))
         ((eq tag 'a) (let ((href (dom-attr node 'href))
                            (text (codeforces--org-children node)))
                        (if href (format "[[%s][%s]]" (codeforces--abs-url href)
                                         (string-trim text))
                          text)))
         ((string-match-p "tex-font-style-tt" class)
          (codeforces--org-emph "=" (dom-texts node "")))
         ((string-match-p "tex-font-style-bf" class)
          (codeforces--org-emph "*" (codeforces--org-children node)))
         ((string-match-p "tex-font-style-it" class)
          (codeforces--org-emph "/" (codeforces--org-children node)))
         ;; Old-style math: keep the rendered Unicode text, tidy whitespace
         ;; (Codeforces pads operators with thin spaces, U+2009).
         ((string-match-p "tex-span" class)
          (string-trim
           (replace-regexp-in-string "[[:space:]]+" " " (dom-texts node ""))))
         (t (codeforces--org-children node)))))))

(defun codeforces--org-children (node)
  "Render NODE's children as a concatenated inline Org string."
  (mapconcat #'codeforces--org-inline (dom-children node) ""))

(defun codeforces--org-list (node)
  "Render a <ul>/<ol> DOM NODE as an Org list."
  (let ((ordered (eq (dom-tag node) 'ol))
        (i 0))
    (concat
     (mapconcat
      (lambda (li)
        (if (and (consp li) (eq (dom-tag li) 'li))
            (progn (setq i (1+ i))
                   (format "%s %s\n"
                           (if ordered (format "%d." i) "-")
                           (string-trim (codeforces--org-inline li))))
          ""))
      (dom-children node) "")
     "\n")))

(defun codeforces--org-example (text)
  "Wrap TEXT in an Org example block."
  (let ((text (if (string-suffix-p "\n" text) text (concat text "\n"))))
    (concat "#+begin_example\n" text "#+end_example\n\n")))

(defun codeforces--org-block (node)
  "Render block-level DOM NODE to Org text with a trailing blank line."
  (cond
   ((stringp node)
    (let ((s (string-trim node)))
      (if (string-empty-p s) "" (concat s "\n\n"))))
   ((not (consp node)) "")
   (t (pcase (dom-tag node)
        ('p (let ((s (string-trim (codeforces--org-inline node))))
              (if (string-empty-p s) "" (concat s "\n\n"))))
        ((or 'ul 'ol) (codeforces--org-list node))
        ('pre (codeforces--org-example (codeforces--dom-pre-text node)))
        ('br "")
        ((or 'img 'a 'span 'i 'b 'em 'strong 'code)
         (let ((s (string-trim (codeforces--org-inline node))))
           (if (string-empty-p s) "" (concat s "\n\n"))))
        (_ (codeforces--org-blocks node))))))

(defun codeforces--org-blocks (node)
  "Render NODE's children as a sequence of Org blocks."
  (mapconcat #'codeforces--org-block (dom-children node) ""))

(defun codeforces--header-value (div)
  "Return a header property DIV's value text, sans its label."
  (when div
    (let ((all (string-trim (dom-texts div)))
          (label (string-trim
                  (dom-texts (car (dom-by-class div "property-title"))))))
      (string-trim (string-remove-prefix label all)))))

(defun codeforces--statement-section (heading div)
  "Render section DIV under an Org HEADING, dropping its section title."
  (when div
    (concat
     (format "* %s\n\n" heading)
     (mapconcat
      #'codeforces--org-block
      (cl-remove-if (lambda (c)
                      (and (consp c)
                           (let ((cl (dom-attr c 'class)))
                             (and cl (string-match-p "section-title" cl)))))
                    (dom-children div))
      ""))))

(defun codeforces--statement-examples (html)
  "Render HTML's sample tests as an Org Examples section, or nil."
  (when-let* ((samples (codeforces--parse-samples html)))
    (let ((i 0))
      (concat
       "* Examples\n\n"
       (mapconcat
        (lambda (pair)
          (setq i (1+ i))
          (format "** Example %d\nInput:\n%sOutput:\n%s"
                  i
                  (codeforces--org-example (string-trim-right (car pair)))
                  (codeforces--org-example (string-trim-right (cdr pair)))))
        samples "")))))

(defun codeforces--statement-org-dom (stmt meta html url)
  "Build an Org statement string from problem-statement DOM STMT.
META is the workspace plist, HTML the page source, URL the problem URL."
  (let* ((header (car (dom-by-class stmt "\\`header\\'")))
         (title (string-trim
                 (dom-texts (car (dom-by-class header "\\`title\\'")))))
         (legend (cl-find-if (lambda (c)
                               (and (consp c) (eq (dom-tag c) 'div)
                                    (not (dom-attr c 'class))))
                             (dom-children stmt))))
    (concat
     (format "#+title: %s%s — %s\n"
             (plist-get meta :contest-id) (plist-get meta :index)
             (or (plist-get meta :name) ""))
     "#+startup: showeverything inlineimages\n\n"
     (format "* %s\n" (if (string-empty-p title) "Statement" title))
     (format "  time limit: %s | memory limit: %s | input: %s | output: %s\n\n"
             (or (codeforces--header-value
                  (car (dom-by-class header "time-limit"))) "?")
             (or (codeforces--header-value
                  (car (dom-by-class header "memory-limit"))) "?")
             (or (codeforces--header-value
                  (car (dom-by-class header "input-file"))) "?")
             (or (codeforces--header-value
                  (car (dom-by-class header "output-file"))) "?"))
     (codeforces--org-blocks legend)
     (codeforces--statement-section
      "Input" (car (dom-by-class stmt "input-specification")))
     (codeforces--statement-section
      "Output" (car (dom-by-class stmt "output-specification")))
     (or (codeforces--statement-examples html) "")
     (codeforces--statement-section "Note" (car (dom-by-class stmt "\\`note\\'")))
     (format "\n[[%s][Open this problem on Codeforces]]\n" url))))

(defun codeforces--statement-org-fallback (html meta url)
  "Best-effort Org statement from HTML without libxml.
META is the workspace plist; URL the problem URL."
  (let* ((i (string-match "class=\"problem-statement\"" html))
         (region (if i (substring html i) html))
         (j (string-match "<script" region))
         (region (if j (substring region 0 j) region)))
    (setq region (replace-regexp-in-string "<br[^>]*>" "\n" region t t)
          region (replace-regexp-in-string "<li[^>]*>" "\n- " region t t)
          region (replace-regexp-in-string "</p>\\|</div>" "\n\n" region t)
          region (replace-regexp-in-string "<[^>]+>" "" region t t)
          region (codeforces--decode-entities region)
          region (replace-regexp-in-string "\n[ \t]*\\(?:\n[ \t]*\\)+" "\n\n" region))
    (concat
     (format "#+title: %s%s — %s\n\n"
             (plist-get meta :contest-id) (plist-get meta :index)
             (or (plist-get meta :name) ""))
     (string-trim region)
     (format "\n\n[[%s][Open this problem on Codeforces]]\n" url))))

(defun codeforces--statement-org (html meta url)
  "Convert problem statement HTML to an Org document string.
META is the workspace metadata plist; URL is the problem URL."
  (let* ((dom (and (fboundp 'libxml-parse-html-region)
                   (with-temp-buffer
                     (insert html)
                     (libxml-parse-html-region (point-min) (point-max)))))
         (stmt (and dom (car (dom-by-class dom "\\`problem-statement\\'"))))
         (org (if stmt
                  (codeforces--statement-org-dom stmt meta html url)
                (codeforces--statement-org-fallback html meta url))))
    (replace-regexp-in-string "\\$\\$\\$" "$" org)))

(defun codeforces--statement-file (root)
  "Return the path to ROOT's statement.org file."
  (expand-file-name "statement.org" root))

;;;###autoload
(defun codeforces-fetch-statement (&optional directory html)
  "Scrape the problem statement for workspace DIRECTORY into statement.org.
DIRECTORY defaults to the current workspace.  With non-nil HTML, convert
that instead of downloading the statement again.  Return the file path;
called interactively, also open it."
  (interactive)
  (let* ((root (or directory (codeforces--workspace-root)))
         (meta (codeforces--read-metadata root))
         (url (codeforces--problem-url (plist-get meta :contest-id)
                                       (plist-get meta :index)))
         (html (or html (codeforces--http-get url)))
         (file (codeforces--statement-file root)))
    (write-region (codeforces--statement-org html meta url) nil file nil 'silent)
    (when (called-interactively-p 'interactive)
      (find-file file))
    (message "codeforces: wrote statement to %s" file)
    file))

(defun codeforces--show-statement-beside (root)
  "Display ROOT's statement.org in a window to the right of the code."
  (let ((file (codeforces--statement-file root)))
    (when (file-exists-p file)
      (display-buffer (find-file-noselect file)
                      '(display-buffer-in-direction
                        (direction . right) (window-width . 0.5))))))

;;;###autoload
(defun codeforces-show-statement ()
  "Show this workspace's statement in Org, side-by-side with the code.
Scrape it first if it has not been fetched yet."
  (interactive)
  (let ((root (codeforces--workspace-root)))
    (unless (file-exists-p (codeforces--statement-file root))
      (codeforces-fetch-statement root))
    (codeforces--show-statement-beside root)))

(defun codeforces--language (key)
  "Return the configuration plist for language KEY, or signal an error."
  (or (cdr (assoc key codeforces-languages))
      (user-error "Unknown language %S; see `codeforces-languages'" key)))

(defun codeforces--read-language ()
  "Prompt for a language key from `codeforces-languages'."
  (completing-read "Language: " (mapcar #'car codeforces-languages)
                   nil t nil nil codeforces-default-language))

(defun codeforces--language-filename (lang)
  "Return the solution file name for language plist LANG."
  (or (plist-get lang :filename)
      (concat "sol." (plist-get lang :extension))))

(defun codeforces--template (key lang)
  "Return the initial solution contents for language KEY with plist LANG.
A literal :template string wins; otherwise the :template-file (default
\"KEY.EXTENSION\") is read from `codeforces-template-directory'."
  (or (plist-get lang :template)
      (let* ((name (or (plist-get lang :template-file)
                       (concat key "." (plist-get lang :extension))))
             (bundled (expand-file-name
                       name (expand-file-name
                             "templates" codeforces--library-directory)))
             (file (if codeforces-template-directory
                       (expand-file-name name codeforces-template-directory)
                     bundled)))
        (unless (file-readable-p file) (setq file bundled))
        (if (file-readable-p file)
            (with-temp-buffer
              (insert-file-contents file)
              (buffer-string))
          (message "codeforces: no template %s; starting empty" file)
          nil))
      ""))

(defun codeforces--language-for-file (file)
  "Return the (KEY . PLIST) language entry matching FILE, or nil.
Prefers an exact :filename match, then the file extension."
  (let ((name (file-name-nondirectory file))
        (ext (file-name-extension file)))
    (or (cl-find-if (lambda (entry)
                      (equal (plist-get (cdr entry) :filename) name))
                    codeforces-languages)
        (cl-find-if (lambda (entry)
                      (equal (plist-get (cdr entry) :extension) ext))
                    codeforces-languages))))

(defun codeforces--write-extra-files (root lang)
  "Write LANG's :extra-files into workspace ROOT, keeping existing ones."
  (pcase-dolist (`(,name . ,content) (plist-get lang :extra-files))
    (let ((file (expand-file-name name root)))
      (unless (file-exists-p file)
        (with-temp-file file (insert content))))))

(defun codeforces--workspace-root ()
  "Return the workspace root containing the current buffer's file."
  (let ((root (locate-dominating-file default-directory ".codeforces")))
    (unless root
      (user-error "Not inside a Codeforces workspace (no .codeforces file)"))
    (expand-file-name root)))

(defun codeforces--read-metadata (root)
  "Read the .codeforces metadata plist from workspace ROOT."
  (let ((file (expand-file-name ".codeforces" root)))
    (unless (file-exists-p file)
      (user-error "No .codeforces metadata in %s" root))
    (with-temp-buffer
      (insert-file-contents file)
      (read (current-buffer)))))

(defun codeforces--write-metadata (root plist)
  "Write metadata PLIST to the .codeforces file in workspace ROOT."
  (with-temp-file (expand-file-name ".codeforces" root)
    (let ((print-length nil)
          (print-level nil))
      (prin1 plist (current-buffer))
      (insert "\n"))))

(defun codeforces--slug (name)
  "Turn problem NAME into a short directory-name slug."
  (let ((s (replace-regexp-in-string "[^a-z0-9]+" "-" (downcase name))))
    (setq s (string-trim s "-+" "-+"))
    (if (> (length s) 40) (substring s 0 40) s)))

(defun codeforces--parse-problem-id (id)
  "Parse problem ID like \"1700A\" or \"1700 A2\" into (CONTEST-ID . INDEX)."
  (let ((id (string-trim id)))
    (unless (string-match
             "\\`\\([0-9]+\\)[ /-]?\\([A-Za-z][0-9]?\\)\\'" id)
      (user-error "Cannot parse problem ID %S (expected e.g. 1700A)" id))
    (cons (string-to-number (match-string 1 id))
          (upcase (match-string 2 id)))))

(defun codeforces--find-problem (contest-id index)
  "Find the cached problem with CONTEST-ID and INDEX, or build a stub."
  (or (cl-find-if (lambda (p)
                    (and (eql (alist-get 'contestId p) contest-id)
                         (equal (alist-get 'index p) index)))
                  (codeforces-problems))
      `((contestId . ,contest-id)
        (index . ,index)
        (name . ,(format "%s%s" contest-id index))
        (tags . nil))))

(defun codeforces--read-problem ()
  "Prompt for a problem by ID and return its alist."
  (let ((parsed (codeforces--parse-problem-id
                 (read-string "Problem ID (e.g. 1700A): "))))
    (codeforces--find-problem (car parsed) (cdr parsed))))

;;;###autoload
(defun codeforces-start-problem (problem &optional language)
  "Create (or revisit) a workspace for PROBLEM and open the solution.
PROBLEM is a problem alist; interactively, prompt for its ID.
LANGUAGE is a key of `codeforces-languages'; it defaults to
`codeforces-default-language' and is prompted for with a prefix
argument or when the default is nil."
  (interactive (list (codeforces--read-problem)))
  (let* ((language (or language
                       (if (or current-prefix-arg
                               (null codeforces-default-language))
                           (codeforces--read-language)
                         codeforces-default-language)))
         (lang (codeforces--language language))
         (cid (alist-get 'contestId problem))
         (index (alist-get 'index problem))
         (name (alist-get 'name problem))
         (root (expand-file-name
                (format "%s%s-%s" cid index (codeforces--slug name))
                codeforces-directory))
         (solution (expand-file-name (codeforces--language-filename lang)
                                     root)))
    (make-directory root t)
    (codeforces--write-metadata
     root (list :contest-id cid
                :index index
                :name name
                :rating (alist-get 'rating problem)
                :tags (alist-get 'tags problem)
                :language language))
    (unless (file-exists-p solution)
      (with-temp-file solution
        (insert (codeforces--template language lang))))
    (codeforces--write-extra-files root lang)
    (let ((need-tests (not (file-directory-p (expand-file-name "tests" root))))
          (need-stmt (not (file-exists-p (codeforces--statement-file root)))))
      (when (or need-tests need-stmt)
        (condition-case err
            (let ((html (codeforces--http-get
                         (codeforces--problem-url cid index))))
              (when need-stmt (codeforces-fetch-statement root html))
              (when need-tests (codeforces-fetch-samples root html)))
          (error (message "codeforces: statement/sample fetch failed: %s"
                          (error-message-string err))))))
    (find-file solution)
    (codeforces-mode 1)
    (codeforces--show-statement-beside root)
    (message "codeforces: %s — %s to begin the timed challenge"
             (codeforces--describe-problem problem)
             (substitute-command-keys "\\[codeforces-challenge-start]"))))

(defun codeforces--format-command (command source root)
  "Expand %f, %b, and %d in COMMAND for SOURCE inside ROOT."
  (format-spec command
               `((?f . ,(shell-quote-argument source))
                 (?b . ,(shell-quote-argument
                         (expand-file-name codeforces-binary-name root)))
                 (?d . ,(shell-quote-argument (directory-file-name root))))))

(defun codeforces--normalize-output (string)
  "Normalize STRING for comparison: trim per-line and trailing whitespace."
  (string-trim-right
   (mapconcat #'string-trim-right
              (split-string (replace-regexp-in-string "\r" "" string) "\n")
              "\n")))

(defun codeforces--test-files (root)
  "Return the .in files under ROOT/tests, sorted numerically."
  (let ((dir (expand-file-name "tests" root)))
    (when (file-directory-p dir)
      (sort (directory-files dir t "\\.in\\'")
            (lambda (a b)
              (< (string-to-number (file-name-base a))
                 (string-to-number (file-name-base b))))))))

(defun codeforces--run-shell (command root &optional input-file)
  "Run shell COMMAND in ROOT, optionally feeding INPUT-FILE on stdin.
Return (EXIT-CODE OUTPUT SECONDS)."
  (let ((default-directory root)
        (start (float-time)))
    (with-temp-buffer
      (let ((exit (call-process-shell-command
                   (if input-file
                       (format "%s < %s"
                               command (shell-quote-argument input-file))
                     command)
                   nil t)))
        (list exit (buffer-string) (- (float-time) start))))))

;;;###autoload
(defun codeforces-run-tests ()
  "Compile (when needed) and run the current solution on all local tests.
Results are shown in the *codeforces-tests* buffer."
  (interactive)
  (unless buffer-file-name
    (user-error "Current buffer is not visiting a file"))
  (save-buffer)
  (let* ((source buffer-file-name)
         (root (codeforces--workspace-root))
         (meta (codeforces--read-metadata root))
         (entry (or (codeforces--language-for-file source)
                    (assoc (plist-get meta :language) codeforces-languages)))
         (lang (or (cdr entry)
                   (user-error "Cannot determine language for %s" source)))
         (tests (or (codeforces--test-files root)
                    (user-error
                     "No tests in %stests/; try `codeforces-fetch-samples' or `codeforces-add-test'"
                     root)))
         (compile-cmd (plist-get lang :compile))
         (run-cmd (codeforces--format-command (plist-get lang :run)
                                              source root))
         (buffer (get-buffer-create "*codeforces-tests*"))
         (passed 0))
    (with-current-buffer buffer
      (let ((inhibit-read-only t))
        (erase-buffer)
        (special-mode)
        (insert (format "%s — %s  (%s)\n"
                        (format "%s%s" (plist-get meta :contest-id)
                                (plist-get meta :index))
                        (or (plist-get meta :name) "")
                        (car entry)))
        (insert (make-string 60 ?─) "\n")
        (if (null compile-cmd)
            (insert "Compile: skipped (interpreted)\n")
          (pcase-let ((`(,exit ,output ,secs)
                       (codeforces--run-shell
                        (codeforces--format-command
                         compile-cmd source root)
                        root)))
            (if (eq exit 0)
                (insert (format "Compile: %s (%.2fs)\n"
                                (propertize "OK" 'face 'success) secs))
              (insert (propertize "Compile failed:\n" 'face 'error)
                      output)
              (setq tests nil))))
        (dolist (in-file tests)
          (let* ((ans-file (concat (file-name-sans-extension in-file) ".ans"))
                 (expected (and (file-exists-p ans-file)
                                (with-temp-buffer
                                  (insert-file-contents ans-file)
                                  (buffer-string))))
                 (command (if codeforces-timeout-program
                              (format "%s %d %s"
                                      codeforces-timeout-program
                                      codeforces-test-timeout
                                      run-cmd)
                            run-cmd)))
            (pcase-let ((`(,exit ,output ,secs)
                         (codeforces--run-shell command root in-file)))
              (let* ((label (file-name-base in-file))
                     (verdict
                      (cond
                       ((eql exit 124) (propertize "TIMEOUT" 'face 'error))
                       ((not (eql exit 0))
                        (propertize (format "RUNTIME ERROR (exit %s)" exit)
                                    'face 'error))
                       ((null expected)
                        (propertize "NO .ans FILE" 'face 'warning))
                       ((equal (codeforces--normalize-output output)
                               (codeforces--normalize-output expected))
                        (cl-incf passed)
                        (propertize "PASS" 'face 'success))
                       (t (propertize "FAIL" 'face 'error)))))
                (insert (format "Test %s: %s (%.2fs)\n" label verdict secs))
                (unless (string-prefix-p "PASS" verdict)
                  (insert "  --- input ---\n"
                          (codeforces--indent-block
                           (with-temp-buffer
                             (insert-file-contents in-file)
                             (buffer-string))))
                  (when expected
                    (insert "  --- expected ---\n"
                            (codeforces--indent-block expected)))
                  (insert "  --- got ---\n"
                          (codeforces--indent-block output)))))))
        (insert (make-string 60 ?─) "\n")
        (insert (format "%d/%d passed.\n" passed (length tests)))
        (goto-char (point-min))))
    (display-buffer buffer)
    (message "codeforces: %d/%d tests passed" passed (length tests))
    (codeforces--challenge-record-result root passed (length tests))))

(defun codeforces--indent-block (string)
  "Indent STRING by four spaces for the test report."
  (concat (replace-regexp-in-string
           "^" "    " (string-trim-right string))
          "\n"))

;;;###autoload
(defun codeforces-add-test ()
  "Add a manual test case to the current workspace.
Opens fresh N.in and N.ans files side by side; fill them in and save."
  (interactive)
  (let* ((root (codeforces--workspace-root))
         (tests-dir (expand-file-name "tests" root))
         (n 1))
    (make-directory tests-dir t)
    (while (file-exists-p (expand-file-name (format "%d.in" n) tests-dir))
      (setq n (1+ n)))
    (find-file (expand-file-name (format "%d.in" n) tests-dir))
    (find-file-other-window (expand-file-name (format "%d.ans" n) tests-dir))
    (message "codeforces: fill in test %d input and expected output, then save" n)))

(defconst codeforces--challenge-buffer "*codeforces-challenge*"
  "Name of the timed-challenge view buffer.")

(defvar codeforces--challenge-timer nil
  "Repeating timer redrawing the live challenge clock, or nil.")

(defvar-local codeforces--challenge-root nil
  "Workspace root whose challenge the challenge buffer is showing.")

(defvar codeforces-challenge-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "g") #'codeforces-challenge-revert)
    (define-key map (kbd "w") #'codeforces-challenge-writeup)
    map)
  "Keymap for `codeforces-challenge-mode'.")

(define-derived-mode codeforces-challenge-mode special-mode "CF-Challenge"
  "Major mode for the timed Codeforces challenge view.

\\{codeforces-challenge-mode-map}")

(defun codeforces--ms-now ()
  "Return the current time in milliseconds since the epoch."
  (truncate (* 1000 (float-time))))

(defun codeforces--format-ms (n)
  "Format N milliseconds as a compact [H:]M:SS.t timer string."
  (let* ((ms (% n 1000))
         (n  (/ n 1000))
         (s  (% n 60))
         (m  (% (/ n 60) 60))
         (h  (/ n 3600)))
    (cond ((> h 0) (format "%d:%02d:%02d.%d" h m s (/ ms 100)))
          ((> m 0) (format "%d:%02d.%d" m s (/ ms 100)))
          (t       (format "%d.%d" s (/ ms 100))))))

(defun codeforces--challenge (root)
  "Return ROOT's challenge plist, or nil when there is none."
  (when (file-exists-p (expand-file-name ".codeforces" root))
    (plist-get (codeforces--read-metadata root) :challenge)))

(defun codeforces--challenge-state (ch)
  "Return the state of challenge plist CH.
One of nil (none), `solving', `solved' (awaiting writeup), or `done'."
  (cond ((null ch) nil)
        ((plist-get ch :done-at) 'done)
        ((plist-get ch :solved-at) 'solved)
        (t 'solving)))

(defun codeforces--challenge-elapsed (ch)
  "Return elapsed milliseconds for challenge CH.
Frozen once the challenge is done, otherwise live wall-clock time."
  (or (plist-get ch :done-at)
      (- (codeforces--ms-now) (plist-get ch :start))))

(defun codeforces--challenge-update (root fn)
  "Replace ROOT's challenge plist with the result of FN and persist it.
FN is called with the current challenge plist (possibly nil)."
  (let* ((meta (codeforces--read-metadata root))
         (ch (funcall fn (plist-get meta :challenge))))
    (codeforces--write-metadata root (plist-put meta :challenge ch))
    ch))

(defun codeforces--challenge-record-result (root passed total)
  "Advance ROOT's running challenge after a test run of PASSED/TOTAL.
A clean sweep marks the solution accepted; anything else is recorded as a
timestamped negative result.  Does nothing unless a challenge is solving."
  (let ((ch (codeforces--challenge root)))
    (when (eq (codeforces--challenge-state ch) 'solving)
      (let ((elapsed (- (codeforces--ms-now) (plist-get ch :start))))
        (if (and (> total 0) (= passed total))
            (progn
              (codeforces--challenge-update
               root (lambda (c) (plist-put c :solved-at elapsed)))
              (message
               "codeforces challenge: ACCEPTED at %s -- now write a writeup (%s)"
               (codeforces--format-ms elapsed)
               (substitute-command-keys "\\[codeforces-challenge-writeup]")))
          (codeforces--challenge-update
           root (lambda (c)
                  (plist-put c :mistakes
                             (append (plist-get c :mistakes) (list elapsed)))))
          (message "codeforces challenge: negative result at %s (%d/%d passed)"
                   (codeforces--format-ms elapsed) passed total))
        (codeforces--challenge-refresh root)))))

(defun codeforces--challenge-render (root)
  "Redraw ROOT's challenge into the challenge buffer when it is live."
  (when-let* ((buf (get-buffer codeforces--challenge-buffer)))
    (let* ((meta (codeforces--read-metadata root))
           (ch (plist-get meta :challenge))
           (state (codeforces--challenge-state ch))
           (mistakes (plist-get ch :mistakes))
           (solved (plist-get ch :solved-at))
           (done (plist-get ch :done-at)))
      (with-current-buffer buf
        (let ((inhibit-read-only t)
              (line (line-number-at-pos)))
          (erase-buffer)
          (insert (propertize (format "Codeforces Challenge — %s%s  %s\n"
                                      (plist-get meta :contest-id)
                                      (plist-get meta :index)
                                      (or (plist-get meta :name) ""))
                              'face 'bold))
          (insert (make-string 60 ?─) "\n")
          (insert "  Elapsed  "
                  (propertize (if ch (codeforces--format-ms
                                      (codeforces--challenge-elapsed ch))
                                "—")
                              'face (if (eq state 'done) 'success 'warning))
                  "\n\n")
          (insert "  1. Solution  "
                  (if solved
                      (propertize (format "✓ accepted at %s"
                                          (codeforces--format-ms solved))
                                  'face 'success)
                    (propertize "… solving (run tests to submit)" 'face 'warning))
                  "\n")
          (dolist (m mistakes)
            (insert (propertize (format "       ✗ negative result at %s\n"
                                        (codeforces--format-ms m))
                                'face 'error)))
          (insert "  2. Writeup   "
                  (cond (done (propertize (format "✓ done at %s"
                                                  (codeforces--format-ms done))
                                          'face 'success))
                        (solved (propertize "… write it up, then save"
                                            'face 'warning))
                        (t (propertize "locked — get accepted first"
                                       'face 'shadow)))
                  "\n")
          (insert (make-string 60 ?─) "\n")
          (when (eq state 'done)
            (insert (propertize
                     (format
                      "  SOLVED in %s  (solution %s, writeup %s, %d mistake%s)\n"
                      (codeforces--format-ms done)
                      (codeforces--format-ms solved)
                      (codeforces--format-ms (- done solved))
                      (length mistakes)
                      (if (= 1 (length mistakes)) "" "s"))
                     'face 'success)))
          (goto-char (point-min))
          (forward-line (1- line)))))))

(defun codeforces--challenge-refresh (root)
  "Redraw the challenge buffer if it is currently showing ROOT."
  (when-let* ((buf (get-buffer codeforces--challenge-buffer)))
    (when (equal (buffer-local-value 'codeforces--challenge-root buf) root)
      (codeforces--challenge-render root))))

(defun codeforces--challenge-stop-timer ()
  "Cancel the challenge redisplay timer."
  (when codeforces--challenge-timer
    (cancel-timer codeforces--challenge-timer)
    (setq codeforces--challenge-timer nil)))

(defun codeforces--challenge-tick ()
  "Keep the live clock fresh; stop the timer when there is nothing to show."
  (let ((buf (get-buffer codeforces--challenge-buffer)))
    (if (not (buffer-live-p buf))
        (codeforces--challenge-stop-timer)
      (let ((root (buffer-local-value 'codeforces--challenge-root buf)))
        (condition-case nil
            (if (and root (memq (codeforces--challenge-state
                                 (codeforces--challenge root))
                                '(solving solved)))
                (codeforces--challenge-render root)
              (when root (codeforces--challenge-render root))
              (codeforces--challenge-stop-timer))
          (error (codeforces--challenge-stop-timer)))))))

(defun codeforces--challenge-start-timer ()
  "Start the repeating challenge redisplay timer if it is not running."
  (unless codeforces--challenge-timer
    (setq codeforces--challenge-timer
          (run-with-timer 0 0.1 #'codeforces--challenge-tick))))

(defun codeforces--challenge-show (root)
  "Pop to the challenge buffer for workspace ROOT and start the live clock."
  (let ((buf (get-buffer-create codeforces--challenge-buffer)))
    (with-current-buffer buf
      (unless (derived-mode-p 'codeforces-challenge-mode)
        (codeforces-challenge-mode))
      (setq-local codeforces--challenge-root root)
      (setq-local default-directory root))
    (codeforces--challenge-render root)
    (codeforces--challenge-start-timer)
    (display-buffer buf)))

;;;###autoload
(defun codeforces-challenge-start ()
  "Start (or restart) the timed challenge for the current workspace.
The clock runs from now until the solution passes every sample test and a
writeup has been saved."
  (interactive)
  (let* ((root (codeforces--workspace-root))
         (state (codeforces--challenge-state (codeforces--challenge root))))
    (when (and (memq state '(solving solved))
               (not (y-or-n-p "A challenge is already running; restart the clock? ")))
      (user-error "Keeping the running challenge"))
    (when (and (eq state 'done)
               (not (y-or-n-p "Already solved; start a fresh timed run? ")))
      (user-error "Keeping the finished challenge"))
    (codeforces--challenge-update
     root (lambda (_) (list :start (codeforces--ms-now) :mistakes nil)))
    (codeforces--challenge-show root)
    (message "codeforces challenge: clock started — solve it and run tests")))

(defun codeforces--challenge-writeup-maybe-finish ()
  "Finish the challenge when the writeup buffer is saved with real content.
Intended for the writeup buffer's local `after-save-hook'."
  (when-let* ((root (and buffer-file-name
                         (locate-dominating-file buffer-file-name ".codeforces"))))
    (setq root (expand-file-name root))
    (let ((ch (codeforces--challenge root)))
      (when (and (eq (codeforces--challenge-state ch) 'solved)
                 (string-match-p
                  "[^[:space:]]"
                  (buffer-substring-no-properties (point-min) (point-max))))
        (let ((elapsed (- (codeforces--ms-now) (plist-get ch :start))))
          (codeforces--challenge-update
           root (lambda (c) (plist-put c :done-at elapsed)))
          (remove-hook 'after-save-hook
                       #'codeforces--challenge-writeup-maybe-finish t)
          (codeforces--challenge-refresh root)
          (message "codeforces challenge: COMPLETE in %s 🎉"
                   (codeforces--format-ms elapsed)))))))

;;;###autoload
(defun codeforces-challenge-writeup ()
  "Open the writeup for the current challenge; saving non-empty text finishes it.
Only available once the solution has been accepted."
  (interactive)
  (let* ((root (codeforces--workspace-root))
         (state (codeforces--challenge-state (codeforces--challenge root))))
    (pcase state
      ('nil (user-error "No challenge; start one with `codeforces-challenge-start'"))
      ('solving (user-error "Get an accepted test run before the writeup"))
      ('done (user-error "Challenge already finished")))
    (find-file (expand-file-name "writeup.md" root))
    (add-hook 'after-save-hook
              #'codeforces--challenge-writeup-maybe-finish nil t)
    (message "Write your writeup, then save to stop the clock")))

;;;###autoload
(defun codeforces-challenge-status ()
  "Open the timed-challenge view for the current workspace."
  (interactive)
  (let ((root (codeforces--workspace-root)))
    (unless (codeforces--challenge root)
      (user-error "No challenge; start one with `codeforces-challenge-start'"))
    (codeforces--challenge-show root)))

(defun codeforces-challenge-revert ()
  "Redraw the challenge view."
  (interactive)
  (when codeforces--challenge-root
    (codeforces--challenge-render codeforces--challenge-root)))

;;;; Workspace commands and minor mode

;;;###autoload
(defun codeforces-open-in-browser ()
  "Open the current workspace's problem statement."
  (interactive)
  (let ((meta (codeforces--read-metadata (codeforces--workspace-root))))
    (funcall codeforces-open-function
             (codeforces--problem-url (plist-get meta :contest-id)
                                      (plist-get meta :index)))))

;;;###autoload
(defun codeforces-submit ()
  "Copy the current solution and open the problem's submit page.
Codeforces has no submission API, so the code is placed on the kill
ring (and system clipboard) for pasting into the submit form."
  (interactive)
  (unless buffer-file-name
    (user-error "Current buffer is not visiting a file"))
  (save-buffer)
  (let ((meta (codeforces--read-metadata (codeforces--workspace-root))))
    (kill-new (buffer-substring-no-properties (point-min) (point-max)))
    (funcall codeforces-open-function
             (codeforces--submit-url (plist-get meta :contest-id)
                                     (plist-get meta :index)))
    (message "codeforces: solution copied; paste it into the submit form")))

(defvar codeforces-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-t") #'codeforces-run-tests)
    (define-key map (kbd "C-c C-a") #'codeforces-add-test)
    (define-key map (kbd "C-c C-o") #'codeforces-open-in-browser)
    (define-key map (kbd "C-c C-d") #'codeforces-show-statement)
    (define-key map (kbd "C-c C-s") #'codeforces-submit)
    (define-key map (kbd "C-c C-r") #'codeforces-fetch-samples)
    (define-key map (kbd "C-c C-n") #'codeforces-roll)
    (define-key map (kbd "C-c C-m") #'codeforces-menu)
    (define-key map (kbd "C-c C-b") #'codeforces-challenge-start)
    (define-key map (kbd "C-c C-w") #'codeforces-challenge-writeup)
    (define-key map (kbd "C-c C-v") #'codeforces-challenge-status)
    map)
  "Keymap for `codeforces-mode'.")

;;;###autoload
(define-minor-mode codeforces-mode
  "Minor mode for buffers inside a Codeforces problem workspace.

\\{codeforces-mode-map}"
  :lighter codeforces-mode-line-lighter
  :keymap codeforces-mode-map)

;;;###autoload
(defun codeforces-maybe-enable-mode ()
  "Enable `codeforces-mode' when visiting a file inside a workspace.
Suitable for `find-file-hook'."
  (when-let* ((_ buffer-file-name)
              (root (locate-dominating-file default-directory ".codeforces")))
    (codeforces-mode 1)
    (when-let* ((key (plist-get (codeforces--read-metadata root) :language))
                (lang (cdr (assoc key codeforces-languages))))
      (codeforces--write-extra-files (expand-file-name root) lang))))

;;;; Problem browser

(defun codeforces--sort-numeric (key)
  "Return a tabulated-list sorter comparing problem field KEY numerically."
  (lambda (a b)
    (< (or (alist-get key (car a)) -1)
       (or (alist-get key (car b)) -1))))

(defvar codeforces-problem-list-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") #'codeforces-problem-list-browse)
    (define-key map (kbd "s") #'codeforces-problem-list-start)
    (define-key map (kbd "x") #'codeforces-problem-list-random)
    (define-key map (kbd "/") #'codeforces-problem-list-set-filters)
    (define-key map (kbd "c") #'codeforces-problem-list-clear-filters)
    map)
  "Keymap for `codeforces-problem-list-mode'.")

(define-derived-mode codeforces-problem-list-mode tabulated-list-mode
  "CF-Problems"
  "Major mode listing Codeforces problems.

\\{codeforces-problem-list-mode-map}"
  (setq tabulated-list-format
        (vector (list "ID" 8 t)
                (list "Rating" 7 (codeforces--sort-numeric 'rating))
                (list "Solved" 8 (codeforces--sort-numeric 'solvedCount))
                (list "Name" 42 t)
                (list "Tags" 0 nil)))
  (setq tabulated-list-padding 1)
  (setq tabulated-list-sort-key '("Rating" . nil))
  (setq tabulated-list-entries #'codeforces--problem-list-entries)
  (tabulated-list-init-header))

(defun codeforces--problem-list-entries ()
  "Build `tabulated-list-entries' from the filtered problem set."
  (mapcar (lambda (p)
            (list p
                  (vector (codeforces--problem-id p)
                          (if-let* ((r (alist-get 'rating p)))
                              (number-to-string r)
                            "—")
                          (if-let* ((s (alist-get 'solvedCount p)))
                              (number-to-string s)
                            "—")
                          (or (alist-get 'name p) "")
                          (string-join (alist-get 'tags p) ", "))))
          (codeforces-filtered-problems)))

(defun codeforces--problem-at-point ()
  "Return the problem alist on the current line, or signal an error."
  (or (tabulated-list-get-id)
      (user-error "No problem on this line")))

(defun codeforces-problem-list-browse ()
  "Open the statement of the problem at point."
  (interactive)
  (let ((p (codeforces--problem-at-point)))
    (funcall codeforces-open-function
             (codeforces--problem-url (alist-get 'contestId p)
                                      (alist-get 'index p)))))

(defun codeforces-problem-list-start ()
  "Start a workspace for the problem at point."
  (interactive)
  (codeforces-start-problem (codeforces--problem-at-point)))

(defun codeforces-problem-list-random ()
  "Jump to a random line of the listing and describe its problem."
  (interactive)
  (let ((n (count-lines (point-min) (point-max))))
    (when (zerop n)
      (user-error "No problems listed"))
    (goto-char (point-min))
    (forward-line (random n))
    (message "%s" (codeforces--describe-problem
                   (codeforces--problem-at-point)))))

(defun codeforces-problem-list-set-filters ()
  "Set filters and refresh the listing."
  (interactive)
  (codeforces-set-filters)
  (revert-buffer)
  (codeforces--problem-list-update-header))

(defun codeforces-problem-list-clear-filters ()
  "Clear filters and refresh the listing."
  (interactive)
  (codeforces-clear-filters)
  (revert-buffer)
  (codeforces--problem-list-update-header))

(defun codeforces--problem-list-update-header ()
  "Show the active filters in the header line."
  (setq header-line-format
        (format " %d problems — %s"
                (length tabulated-list-entries)
                (codeforces--filter-description))))

;;;###autoload
(defun codeforces-list-problems ()
  "Browse the problemset with the current filters applied."
  (interactive)
  (codeforces-problems)
  (with-current-buffer (get-buffer-create "*codeforces-problems*")
    (codeforces-problem-list-mode)
    (tabulated-list-print)
    (setq header-line-format
          (format " %d problems — %s"
                  (length (codeforces-filtered-problems))
                  (codeforces--filter-description)))
    (pop-to-buffer (current-buffer))))

;;;; Contests

(defun codeforces--format-duration (seconds)
  "Format SECONDS as e.g. \"2h00\"."
  (format "%dh%02d" (/ seconds 3600) (/ (% seconds 3600) 60)))

(defvar codeforces-contest-list-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") #'codeforces-contest-list-browse)
    (define-key map (kbd "S") #'codeforces-contest-list-standings)
    map)
  "Keymap for `codeforces-contest-list-mode'.")

(define-derived-mode codeforces-contest-list-mode tabulated-list-mode
  "CF-Contests"
  "Major mode listing Codeforces contests.

\\{codeforces-contest-list-mode-map}"
  (setq tabulated-list-format
        (vector (list "ID" 6 t)
                (list "Start" 17 t)
                (list "Dur" 6 nil)
                (list "Phase" 9 t)
                (list "Name" 0 t)))
  (setq tabulated-list-padding 1)
  (tabulated-list-init-header))

(defun codeforces-contest-list-browse ()
  "Open the contest at point in the browser."
  (interactive)
  (let ((c (or (tabulated-list-get-id)
               (user-error "No contest on this line"))))
    (funcall codeforces-open-function
             (format "https://codeforces.com/contest/%s"
                     (alist-get 'id c)))))

(defun codeforces-contest-list-standings ()
  "Show standings for the contest at point."
  (interactive)
  (let ((c (or (tabulated-list-get-id)
               (user-error "No contest on this line"))))
    (codeforces-standings (alist-get 'id c))))

;;;###autoload
(defun codeforces-contests (&optional gym)
  "List upcoming and recent contests.  With prefix GYM, list gym contests."
  (interactive "P")
  (let ((contests (codeforces-api-contest-list gym)))
    (with-current-buffer (get-buffer-create "*codeforces-contests*")
      (codeforces-contest-list-mode)
      (setq tabulated-list-entries
            (mapcar
             (lambda (c)
               (list c
                     (vector
                      (number-to-string (alist-get 'id c))
                      (if-let* ((start (alist-get 'startTimeSeconds c)))
                          (format-time-string "%Y-%m-%d %H:%M"
                                              (seconds-to-time start))
                        "—")
                      (codeforces--format-duration
                       (or (alist-get 'durationSeconds c) 0))
                      (or (alist-get 'phase c) "")
                      (or (alist-get 'name c) ""))))
             (seq-take contests 200)))
      (tabulated-list-print)
      (pop-to-buffer (current-buffer)))))

;;;###autoload
(defun codeforces-standings (contest-id)
  "Show the top of the standings of CONTEST-ID, plus your own row."
  (interactive (list (read-number "Contest ID: ")))
  (let* ((result (codeforces-api-contest-standings
                  contest-id
                  :from 1 :count codeforces-standings-count
                  :show-unofficial nil))
         (contest (alist-get 'contest result))
         (rows (alist-get 'rows result))
         (own (when codeforces-handle
                (ignore-errors
                  (alist-get 'rows
                             (codeforces-api-contest-standings
                              contest-id
                              :handles (list codeforces-handle)))))))
    (with-current-buffer (get-buffer-create "*codeforces-standings*")
      (let ((inhibit-read-only t))
        (erase-buffer)
        (special-mode)
        (insert (format "%s\n%s\n\n" (alist-get 'name contest)
                        (make-string 60 ?─)))
        (dolist (row (append rows own))
          (let ((party (alist-get 'party row)))
            (insert (format "%5s  %-30s %8s\n"
                            (alist-get 'rank row)
                            (mapconcat (lambda (m) (alist-get 'handle m))
                                       (alist-get 'members party) ", ")
                            (alist-get 'points row)))))
        (goto-char (point-min)))
      (pop-to-buffer (current-buffer)))))

;;;; User views

(defun codeforces--require-handle (handle)
  "Return HANDLE or `codeforces-handle', or signal a user error."
  (or handle codeforces-handle
      (user-error "Set `codeforces-handle' or pass a handle")))

;;;###autoload
(defun codeforces-show-user (&optional handle)
  "Show rating and rank information for HANDLE (default `codeforces-handle')."
  (interactive (list (read-string "Handle (empty for yours): " nil nil nil)))
  (let* ((handle (codeforces--require-handle
                  (and handle (not (string-empty-p handle)) handle)))
         (user (car (codeforces-api-user-info handle))))
    (message "%s: rating %s (max %s), rank %s (max %s), %s friend(s)"
             (alist-get 'handle user)
             (or (alist-get 'rating user) "unrated")
             (or (alist-get 'maxRating user) "—")
             (or (alist-get 'rank user) "—")
             (or (alist-get 'maxRank user) "—")
             (or (alist-get 'friendOfCount user) 0))))

;;;###autoload
(defun codeforces-rating-history (&optional handle)
  "Show the contest rating history of HANDLE (default `codeforces-handle')."
  (interactive (list (read-string "Handle (empty for yours): " nil nil nil)))
  (let* ((handle (codeforces--require-handle
                  (and handle (not (string-empty-p handle)) handle)))
         (changes (codeforces-api-user-rating handle)))
    (with-current-buffer (get-buffer-create "*codeforces-rating*")
      (let ((inhibit-read-only t))
        (erase-buffer)
        (special-mode)
        (insert (format "Rating history for %s (%d rated contests)\n%s\n"
                        handle (length changes) (make-string 70 ?─)))
        (dolist (c changes)
          (let* ((old (alist-get 'oldRating c))
                 (new (alist-get 'newRating c))
                 (delta (- new old)))
            (insert (format "%s  #%-5s %4d → %4d  %s  %s\n"
                            (format-time-string
                             "%Y-%m-%d"
                             (seconds-to-time
                              (alist-get 'ratingUpdateTimeSeconds c)))
                            (alist-get 'rank c)
                            old new
                            (propertize (format "%+4d" delta)
                                        'face (if (>= delta 0)
                                                  'success 'error))
                            (alist-get 'contestName c)))))
        (goto-char (point-max)))
      (pop-to-buffer (current-buffer)))))

;;;###autoload
(defun codeforces-my-submissions (&optional handle)
  "Show recent submissions of HANDLE (default `codeforces-handle')."
  (interactive)
  (let* ((handle (codeforces--require-handle handle))
         (subs (codeforces-api-user-status
                handle 1 codeforces-submissions-count)))
    (with-current-buffer (get-buffer-create "*codeforces-submissions*")
      (let ((inhibit-read-only t))
        (erase-buffer)
        (special-mode)
        (insert (format "Recent submissions for %s\n%s\n"
                        handle (make-string 78 ?─)))
        (dolist (s subs)
          (let* ((p (alist-get 'problem s))
                 (verdict (or (alist-get 'verdict s) "TESTING")))
            (insert (format "%s  %-7s %-32s %-22s %s\n"
                            (format-time-string
                             "%m-%d %H:%M"
                             (seconds-to-time
                              (alist-get 'creationTimeSeconds s)))
                            (codeforces--problem-id p)
                            (truncate-string-to-width
                             (or (alist-get 'name p) "") 32)
                            (truncate-string-to-width
                             (or (alist-get 'programmingLanguage s) "") 22)
                            (propertize verdict 'face
                                        (if (equal verdict "OK")
                                            'success 'error))))))
        (goto-char (point-min)))
      (pop-to-buffer (current-buffer)))))

;;;; Transient menu

;;;###autoload (autoload 'codeforces-menu "codeforces" nil t)
(transient-define-prefix codeforces-menu ()
  "Top-level Codeforces menu."
  [:description
   (lambda () (format "Codeforces — %s" (codeforces--filter-description)))
   ["Practice"
    ("r" "Random problem" codeforces-random-problem)
    ("R" "Roll & start" codeforces-roll)
    ("l" "Browse problems" codeforces-list-problems)
    ("p" "Start problem by ID" codeforces-start-problem)
    ("/" "Set filters" codeforces-set-filters :transient t)
    ("c" "Clear filters" codeforces-clear-filters :transient t)]
   ["Workspace"
    ("t" "Run tests" codeforces-run-tests)
    ("a" "Add test case" codeforces-add-test)
    ("F" "Re-fetch samples" codeforces-fetch-samples)
    ("d" "Show statement (Org)" codeforces-show-statement)
    ("D" "Re-fetch statement" codeforces-fetch-statement)
    ("o" "Open in browser" codeforces-open-in-browser)
    ("s" "Submit (copy + browse)" codeforces-submit)]
   ["Challenge"
    ("b" "Begin timed challenge" codeforces-challenge-start)
    ("w" "Write the writeup" codeforces-challenge-writeup)
    ("v" "Challenge view" codeforces-challenge-status)]
   ["Info"
    ("C" "Contests" codeforces-contests)
    ("S" "Standings" codeforces-standings)
    ("u" "User info" codeforces-show-user)
    ("h" "Rating history" codeforces-rating-history)
    ("m" "My submissions" codeforces-my-submissions)
    ("g" "Refresh caches" codeforces-refresh)]])

(provide 'codeforces)

;;; codeforces.el ends here
