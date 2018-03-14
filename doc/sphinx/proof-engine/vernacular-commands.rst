

.. _vernacularcommands:

Vernacular commands
=============================
:Source: https://coq.inria.fr/distrib/current/refman/vernacular.html
:Converted by: Yves Bertot


.. _displaying:

Displaying
--------------


.. _Print:

.. cmd:: Print @qualid.
~~~~~~~~~~~~~~~~~~~

This command displays on the screen information about the declared or
defined object referred by `qualid`.


Error messages:


.. exn:: @qualid not a defined object



Variants:


.. cmdv:: Print Term @qualid.

This is a synonym to ``Print`` `qualid` when `qualid`
denotes a global constant.

.. cmdv:: About @qualid.

This displays various information about the object
denoted by `qualid`: its kind (module, constant, assumption, inductive,
constructor, abbreviation, …), long name, type, implicit arguments and
argument scopes. It does not print the body of definitions or proofs.



.. cmd:: Print All.
~~~~~~~~~~~~~~~~

This command displays information about the current state of the
environment, including sections and modules.


Variants:


.. cmdv:: Inspect @num.

This command displays the num last objects of the
current environment, including sections and modules.

.. cmdv:: Print Section @ident.

should correspond to a currently open section,
this command displays the objects defined since the beginning of this
section.


.. _flags-options-tables:

Flags, Options and Tables
-----------------------------

Coq configurability is based on flags (e.g. Set Printing All in
Section :ref:`TODO-2.9-printing-full`_), options (e.g. ``Set Printing Widthinteger`` in Section
:ref:`TODO-6.9.6-set-printing-width`_), or tables (e.g. ``Add Printing Record ident``, in Section
:ref:`TODO-2.2.4-add-printing-record`_). The names of flags, options and tables are made of non-empty sequences of identifiers
(conventionally with capital initial
letter). The general commands handling flags, options and tables are
given below.


.. cmd:: Set @flag.
~~~~~~~~~~~~~~~

This command switches `flag` on. The original state of `flag` is restored
when the current module ends.


Variants:


.. cmdv:: Local Set @flag.

This command switches `flag` on. The original state
of `flag` is restored when the current *section* ends.

.. cmdv:: Global Set @flag.

This command switches `flag` on. The original state
of `flag` is *not* restored at the end of the module. Additionally, if
set in a file, `flag` is switched on when the file is `Require`-d.



.. cmd:: Unset @flag.
~~~~~~~~~~~~~~~~~

This command switches `flag` off. The original state of `flag` is restored
when the current module ends.


Variants:

.. cmdv:: Local Unset @flag.

This command switches `flag` off. The original
state of `flag` is restored when the current *section* ends.

.. cmdv:: Global Unset @flag.

This command switches `flag` off. The original
state of `flag` is *not* restored at the end of the module. Additionally,
if set in a file, `flag` is switched off when the file is `Require`-d.



.. cmd:: Test @flag.
~~~~~~~~~~~~~~~~

This command prints whether `flag` is on or off.


.. cmd:: Set @option @value.
~~~~~~~~~~~~~~~~~~~~~~~

This command sets `option` to `value`. The original value of ` option` is
restored when the current module ends.


Variants:


.. cmdv:: Local Set @option @value.

This command sets `option` to `value`. The
original value of `option` is restored at the end of the module.

.. cmdv:: Global Set @option @value.

This command sets `option` to `value`. The
original value of `option` is *not* restored at the end of the module.
Additionally, if set in a file, `option` is set to value when the file
is `Require`-d.



.. cmd::  Unset option.
~~~~~~~~~~~~~~~~~~~

This command resets option to its default value.


Variants:


.. cmdv:: Local Unset @option.

This command resets `option` to its default
value. The original state of `option` is restored when the current
*section* ends.

.. cmdv:: Global Unset @option.

This command resets `option` to its default
value. The original state of `option` is *not* restored at the end of the
module. Additionally, if unset in a file, `option` is reset to its
default value when the file is `Require`-d.



.. cmd:: Test @option.
~~~~~~~~~~~~~~~~~~

This command prints the current value of `option`.


.. cmd:: Add @table @value.
~~~~~~~~~~~~

The general commands for tables are ``Add`` `table` `value`, ``Remove`` `table`
`value`, ``Test`` `table`, ``Test`` `table` ``for`` `value` and ``Print Table`` `table`.


.. cmd:: Print Options.
~~~~~~~~~~~~~~~~~~~~

This command lists all available flags, options and tables.


Variants:


.. cmdv:: Print Tables.

This is a synonymous of ``Print Options``.


.. _requests-to-the-environment:

Requests to the environment
-------------------------------


.. cmd:: Check @term.
~~~~~~~~~~~~~~~~~

This command displays the type of `term`. When called in proof mode, the
term is checked in the local context of the current subgoal.


Variants:


.. cmdv:: @selector: Check @term.

specifies on which subgoal to perform typing
(see Section :ref:`TODO-8.1-invocation-of-tactics`_).



.. cmd:: Eval @convtactic in @term.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command performs the specified reduction on `term`, and displays
the resulting term with its type. The term to be reduced may depend on
hypothesis introduced in the first subgoal (if a proof is in
progress).


See also: Section :ref:`TODO-8.7-performing-computations`_.


.. cmd:: Compute @term.
~~~~~~~~~~~~~~~~~~~

This command performs a call-by-value evaluation of term by using the
bytecode-based virtual machine. It is a shortcut for ``Eval vm_compute in``
`term`.


See also: Section :ref:`TODO-8.7-performing-computations`_.


.. cmd::Extraction @term.
~~~~~~~~~~~~~~~~~~~~~~

This command displays the extracted term from `term`. The extraction is
processed according to the distinction between ``Set`` and ``Prop``; that is
to say, between logical and computational content (see Section
:ref:`TODO-4.1.1-sorts`_). The extracted term is displayed in Objective Caml
syntax,
where global identifiers are still displayed as in Coq terms.


Variants:


.. cmdv:: Recursive Extraction @qualid1 … @qualid n .

Recursively extracts all
   the material needed for the extraction of global `qualid1` , …, `qualidn` .



See also: Chapter ref:`TODO-23-chapter-extraction`_.


.. cmd:: Print Assumptions @qualid.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This commands display all the assumptions (axioms, parameters and
variables) a theorem or definition depends on. Especially, it informs
on the assumptions with respect to which the validity of a theorem
relies.


Variants:


.. cmdv:: Print Opaque Dependencies @qualid.

Displays the set of opaque constants qualid relies on in addition to
the assumptions.

.. cmdv:: Print Transparent Dependencies @qualid.

Displays the set of
transparent constants qualid relies on in addition to the assumptions.

.. cmdv:: Print All Dependencies qualid.

Displays all assumptions and constants qualid relies on.



.. cmd:: Search @qualid.
~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all objects (hypothesis of
the current goal, theorems, axioms, etc) of the current context whose
statement contains qualid. This command is useful to remind the user
of the name of library lemmas.


Error messages:


.. exn:: The reference qualid was not found in the current environment

There is no constant in the environment named qualid.

Variants:

.. cmdv:: Search @string.

If string is a valid identifier, this command
displays the name and type of all objects (theorems, axioms, etc) of
the current context whose name contains string. If string is a
notation’s string denoting some reference `qualid` (referred to by its
main symbol as in `"+"` or by its notation’s string as in `"_ + _"` or
`"_ 'U' _"`, see Section :ref:`TODO-12.1-notations`_), the command works like
   ``Search`` `qualid`.

.. cmdv:: Search @string%@key.

The string string must be a notation or the main
symbol of a notation which is then interpreted in the scope bound to
the delimiting key `key` (see Section :ref:`TODO-12.2.2-local-interpretation-rules-for-notations`_).

.. cmdv:: Search @term_pattern.

This searches for all statements or types of
definition that contains a subterm that matches the pattern
`term_pattern` (holes of the pattern are either denoted by `_` or by
`?ident` when non linear patterns are expected).

.. cmdv:: Search [-]@term_pattern_string … [-]@term_pattern_string.

where
`term_pattern_string` is a term_pattern or a string, or a string followed
by a scope delimiting key `%key`.  This generalization of ``Search`` searches
for all objects whose statement or type contains a subterm matching
`term_pattern` (or `qualid` if `string` is the notation for a reference
qualid) and whose name contains all string of the request that
correspond to valid identifiers. If a term_pattern or a string is
prefixed by `-`, the search excludes the objects that mention that
term_pattern or that string.

.. cmdv:: Search @term_pattern_string … @term_pattern_string inside @module1 … @modulen .

This restricts the search to constructions defined in
modules `module1` … `modulen` .

.. cmdv:: Search @term_pattern_string … @term_pattern_string outside @module1 … @modulen .

This restricts the search to constructions not defined in
modules `module1` … `modulen` .

.. cmdv:: @selector: Search [-]@term_pattern_string … [-]@term_pattern_string.

This specifies the goal on which to search hypothesis (see
Section :ref:`TODO-8.1-invocation-of-tactics`_).
By default the 1st goal is searched. This variant can
be combined with other variants presented here.


.. coqtop:: in

   Require Import ZArith.

.. coqtop:: all

   Search Z.mul Z.add "distr".

   Search "+"%Z "*"%Z "distr" -positive -Prop.

   Search (?x * _ + ?x * _)%Z outside OmegaLemmas.

Warning: Up to Coq version 8.4, `Search` had the behavior of current
`SearchHead` and the behavior of current Search was obtained with
command `SearchAbout`. For compatibility, the deprecated name
SearchAbout can still be used as a synonym of Search. For
compatibility, the list of objects to search when using `SearchAbout`
may also be enclosed by optional[ ] delimiters.


.. cmd:: SearchHead @term.
~~~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion has the form `(term t1 .. tn)`. This command is
useful to remind the user of the name of library lemmas.



.. coqtop:: reset all

   SearchHead le.

   SearchHead (@eq bool).


Variants:

.. cmdv:: SearchHead @term inside @module1 … @modulen .

This restricts the
search to constructions defined in modules
`module1` … `modulen` .

.. cmdv:: SearchHead term outside @module1 … @modulen .

This restricts the
search to constructions not defined in modules `module1` … `modulen` .


Error messages:

.. exn:: Module/section module not found

No module `module` has been required
(see Section :ref:`TODO-6.5.1-require`_).

.. cmdv:: @selector: SearchHead @term.

This specifies the goal on which to
search hypothesis (see Section :ref:`TODO-8.1-invocation-of-tactics`_).

By default the 1st goal is
searched. This variant can be combined with other variants presented
here.

Warning: Up to Coq version 8.4, ``SearchHead`` was named ``Search``.


.. cmd:: SearchPattern @term.
~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion or last hypothesis and conclusion matches the
expressionterm where holes in the latter are denoted by `_`.
It is a
variant of Search @term_pattern that does not look for subterms but
searches for statements whose conclusion has exactly the expected
form, or whose statement finishes by the given series of
hypothesis/conclusion.

.. coqtop:: in

   Require Import Arith.

.. coqtop:: all

    SearchPattern (_ + _ = _ + _).

    SearchPattern (nat -> bool).

    SearchPattern (forall l : list _, _ l l).

Patterns need not be linear: you can express that the same expression
must occur in two places by using pattern variables `?ident`.


.. coqtop:: all

   SearchPattern (?X1 + _ = _ + ?X1).

Variants:


.. cmdv:: SearchPattern @term inside @module1 … @modulen .

This restricts the
search to constructions defined in modules `module1` … `modulen` .

.. cmdv:: SearchPattern @term outside @module1 … @modulen.

This restricts the
search to constructions not defined in modules `module1` … `modulen` .

.. cmdv:: @selector: SearchPattern @term.

This specifies the goal on which to
   search hypothesis (see Section :ref:`TODO-8.1-invocation-of-tactics`_). By default the 1st goal is
   searched. This variant can be combined with other variants presented
   here.



.. cmdv:: SearchRewrite @term.
~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion is an equality of which one side matches the
expression term. Holes in term are denoted by “_”.

.. coqtop:: in

    Require Import Arith.

.. coqtop:: all

    SearchRewrite (_ + _ + _).

Variants:


.. cmdv:: SearchRewrite term insidemodule 1 … module n .

This restricts the
search to constructions defined in modules `module1` … `modulen` .

.. cmdv:: SearchRewrite @term outside @module1 … @modulen.

This restricts the
search to constructions not defined in modules `module1` … `modulen` .

.. cmdv:: @selector: SearchRewrite @
term.
This specifies the goal on which to
   search hypothesis (see Section :ref:`TODO-8.1-invocation-of-tactics`_). By default the 1st goal is
   searched. This variant can be combined with other variants presented
   here.

Nota Bene:
``````````

For the ``Search``, ``SearchHead``, ``SearchPattern`` and ``SearchRewrite``
queries, it
is possible to globally filter the search results via the command
``Add Search Blacklist`` "substring1". A lemma whose fully-qualified name
contains any of the declared substrings will be removed from the
search results. The default blacklisted substrings are "_subproof"
"Private_". The command Remove Search Blacklist ... allows expunging
this blacklist.


.. cmd:: Locate @qualid.
~~~~~~~~~~~~~~~~~~~~~

This command displays the full name of objects whose name is a prefix
of the qualified identifier `qualid`, and consequently the Coq module in
which they are defined. It searches for objects from the different
qualified name spaces of Coq: terms, modules, Ltac, etc.

.. coqtop:: none

    Set Printing Depth 50.

.. coqtop:: all

    Locate nat.

    Locate Datatypes.O.

    Locate Init.Datatypes.O.

    Locate Coq.Init.Datatypes.O.

    Locate I.Dont.Exist.

Variants:


.. cmdv:: Locate Term @qualid.

As Locate but restricted to terms.

.. cmdv:: Locate Module @qualid.

As Locate but restricted to modules.

.. cmdv:: Locate Ltac @qualid.

As Locate but restricted to tactics.


See also: Section `12.1.10`_


.. _loading-files:

Loading files
-----------------

Coq offers the possibility of loading different parts of a whole
development stored in separate files. Their contents will be loaded as
if they were entered from the keyboard. This means that the loaded
files are ASCII files containing sequences of commands for Coq’s
toplevel. This kind of file is called a *script* for Coq. The standard
(and default) extension of Coq’s script files is .v.


.. cmd:: Load @ident.
~~~~~~~~~~~~~~~~~

This command loads the file named `ident`.v, searching successively in
each of the directories specified in the *loadpath*. (see Section
:ref:`TODO-2.6.3-libraries-and-filesystem`_)


Variants:


.. cmdv:: Load @string.

Loads the file denoted by the string `string`, where
string is any complete filename. Then the `~` and .. abbreviations are
allowed as well as shell variables. If no extension is specified, Coq
will use the default extension `e`.v

.. cmdv:: Load Verbose @ident.

.. cmdv:: Load Verbose string.

Display, while loading,
the answers of Coq to each command (including tactics) contained in
the loaded file See also: Section :ref:`TODO-6.9.1-silent`_.

Error messages:

.. exn:: Can’t find file @ident on loadpath


.. _compiled-files:

Compiled files
------------------

This section describes the commands used to load compiled files (see
Chapter :ref:`TODO-14-coq-commands`_ for documentation on how to compile a file). A compiled
file is a particular case of module called *library file*.


.. cmd:: Require @qualid.
~~~~~~~~~~~~~~~~~~~~~

This command looks in the loadpath for a file containing module `qualid`
and adds the corresponding module to the environment of Coq. As
library files have dependencies in other library files, the command
Require `qualid` recursively requires all library files the module
qualid depends on and adds the corresponding modules to the
environment of Coq too. Coq assumes that the compiled files have been
produced by a valid Coq compiler and their contents are then not
replayed nor rechecked.

To locate the file in the file system, `qualid` is decomposed under the
form `dirpath.ident` and the file `ident.vo` is searched in the physical
directory of the file system that is mapped in Coq loadpath to the
logical path dirpath (see Section :ref:`TODO-2.6.3-libraries-and-filesystem`_). The mapping between
physical directories and logical names at the time of requiring the
file must be consistent with the mapping used to compile the file. If
several files match, one of them is picked in an unspecified fashion.


Variants:

.. cmdv:: Require Import @qualid.

This loads and declares the module `qualid`
and its dependencies then imports the contents of `qualid` as described
in Section :ref:`TODO-2.5.8-import`_.It does not import the modules on which
qualid depends unless these modules were themselves required in module
`qualid`
using ``Require Export``, as described below, or recursively required
through a sequence of ``Require Export``.  If the module required has
already been loaded, ``Require Import`` `qualid` simply imports it, as ``Import``
`qualid` would.

.. cmdv:: Require Export @qualid.

This command acts as ``Require Import`` `qualid`,
but if a further module, say `A`, contains a command ``Require Export`` `B`,
then the command ``Require Import`` `A` also imports the module `B.`

.. cmdv:: Require [Import | Export] @qualid1 … @qualidn .

This loads the
modules `qualid1` , …, `qualidn` and their recursive dependencies. If
``Import`` or ``Export`` is given, it also imports `qualid1`, …, `qualidn` and
all the recursive dependencies that were marked or transitively marked
as Export.

.. cmdv:: From @dirpath Require @qualid.

This command acts as ``Require``, but picks
any library whose absolute name is of the form dirpath.dirpath’.qualid
for some `dirpath’`. This is useful to ensure that the `qualid` library
comes from a given package by making explicit its absolute root.



Error messages:

.. exn:: Cannot load qualid: no physical path bound to dirpath

.. exn:: Cannot find library foo in loadpath

The command did not find the
file foo.vo. Either foo.v exists but is not compiled or foo.vo is in a
directory which is not in your LoadPath (see Section :ref:`TODO-2.6.3-libraries-and-filesystem`_).

.. exn:: Compiled library ident.vo makes inconsistent assumptions over library qualid

The command tried to load library file `ident.vo` that
depends on some specific version of library `qualid` which is not the
one already loaded in the current Coq session. Probably `ident.v` was
not properly recompiled with the last version of the file containing
module `qualid`.

.. exn:: Bad magic number

The file `ident.vo` was found but either it is not a
Coq compiled module, or it was compiled with an incompatible
version of Coq.

.. exn:: The file `ident.vo` contains library dirpath and not library dirpath’

The library file `dirpath’` is indirectly required by the
``Require`` command but it is bound in the current loadpath to the
file `ident.vo` which was bound to a different library name `dirpath` at
the time it was compiled.


.. exn:: Require is not allowed inside a module or a module type

This command
is not allowed inside a module or a module type being defined. It is
meant to describe a dependency between compilation units. Note however
that the commands Import and Export alone can be used inside modules
(see Section :ref:`TODO-2.5.8-import`_).



See also: Chapter :ref:`TODO-14-coq-commands`_


.. cmd:: Print Libraries.
~~~~~~~~~~~~~~~~~~~~~~

This command displays the list of library files loaded in the
current Coq session. For each of these libraries, it also tells if it
is imported.


.. cmd:: Declare ML Module @string1 .. @stringn .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This commands loads the Objective Caml compiled files `string1` … `stringn`
(dynamic link). It is mainly used to load tactics dynamically. The
files are searched into the current Objective Caml loadpath (see the
command Add ML Path in the Section :ref:`TODO-2.6.3-libraries-and-filesystem`_). Loading of Objective
Caml files is only possible under the bytecode version of coqtop (i.e.
coqtop.byte, see chapter :ref:`TODO-14-coq-commands`_), or when Coq has been compiled with a
version of Objective Caml that supports native Dynlink (≥ 3.11).


Variants:


.. cmdv:: Local Declare ML Module `string1` .. `stringn` .

This variant is not
exported to the modules that import the module where they occur, even
if outside a section.



Error messages:

.. exn:: File not found on loadpath : `string`s
.. exn:: Loading of ML object file forbidden in a native Coq



.. cmd:: Print ML Modules.
~~~~~~~~~~~~~~~~~~~~~~~

This prints the name of all Objective Caml modules loaded with ``Declare
ML Module``. To know from where these module were loaded, the user
should use the command Locate File (see Section :ref:`TODO-6.6.10-locate-file`_)


.. _loadpath:

Loadpath
------------

Loadpaths are preferably managed using Coq command line options (see
Section `2.6.3`_) but there remain vernacular commands to manage them
for practical purposes. Such commands are only meant to be issued in
the toplevel, and using them in source files is discouraged.


.. cmd:: Pwd.
~~~~~~~~~~

This command displays the current working directory.


.. cmd:: Cd @string.
~~~~~~~~~~~~~~~~

This command changes the current directory according to `string` which
can be any valid path.


Variants:


.. cmdv:: Cd.

Is equivalent to Pwd.



.. cmd:: Add LoadPath @string as @dirpath.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command is equivalent to the command line option
``-Q`` `string` `dirpath`. It adds the physical directory string to the current
Coq loadpath and maps it to the logical directory dirpath.


Variants:


.. cmdv:: Add LoadPath @string.

Performs as Add LoadPath string as dirpath but
for the empty directory path.



.. cmd:: Add Rec LoadPath @string as @dirpath.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command is equivalent to the command line option
``-R`` `string` `dirpath`. It adds the physical directory string and all its
subdirectories to the current Coq loadpath.


Variants:


.. cmdv:: Add Rec LoadPath @string.

Works as ``Add Rec LoadPath`` `string` as `dirpath` but for the empty
logical directory path.



.. cmd:: Remove LoadPath `string`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command removes the path string from the current Coq loadpath.


.. cmd:: Print LoadPath.
~~~~~~~~~~~~~~~~~~~~~

This command displays the current Coq loadpath.


Variants:


.. cmdv:: Print LoadPath @dirpath.

Works as ``Print LoadPath`` but displays only
the paths that extend the `dirpath` prefix.


.. cmd:: Add ML Path @string.
~~~~~~~~~~~~~~~~~~~~~~~~~

This command adds the path `string` to the current Objective Caml
loadpath (see the command `Declare ML Module`` in Section :ref:`TODO-6.5-compiled-files`_).


.. cmd:: Add Rec ML Path @string.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command adds the directory `string` and all its subdirectories to
the current Objective Caml loadpath (see the command ``Declare ML Module
in Section :ref:`TODO-6.5-compiled-files`_).


.. cmd:: Print ML Path @string.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current Objective Caml loadpath. This
command makes sense only under the bytecode version of coqtop, i.e.
coqtop.byte (see the command Declare ML Module in Section :ref:`TODO-6.5-compiled-files`_).


.. cmd:: Locate File @string.
~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the location of file string in the current
loadpath. Typically, string is a .cmo or .vo or .v file.


.. cmd:: Locate Library @dirpath.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command gives the status of the Coq module dirpath. It tells if
the module is loaded and if not searches in the load path for a module
of logical name `dirpath`.


.. _backtracking:

Backtracking
----------------

The backtracking commands described in this section can only be used
interactively, they cannot be part of a vernacular file loaded via
``Load`` or compiled by ``coqc``.


.. cmd:: Reset @ident.
~~~~~~~~~~~~~~~~~~

This command removes all the objects in the environment since `ident`
was introduced, including `ident`. `ident` may be the name of a defined or
declared object as well as the name of a section. One cannot reset
over the name of a module or of an object inside a module.


Error messages:


.. exn:: @ident: no such entry



Variants:


.. exn:: Reset Initial.

Goes back to the initial state, just after the start
of the interactive session.



.. cmd:: Back.
~~~~~~~~~~~

This commands undoes all the effects of the last vernacular command.
Commands read from a vernacular file via a `Load` are considered as a
single command. Proof management commands are also handled by this
command (see Chapter `7`_). For that, Back may have to undo more than
one command in order to reach a state where the proof management
information is available. For instance, when the last command is a
``Qed``, the management information about the closed proof has been
discarded. In this case, ``Back`` will then undo all the proof steps up to
the statement of this proof.


Variants:


.. cmdv:: Back @n.

Undoes `n` vernacular commands. As for Back, some extra
commands may be undone in order to reach an adequate state. For
instance Back `n` will not re-enter a closed proof, but rather go just
before that proof.



Error messages:


.. exn:: Invalid backtrack

The user wants to undo more commands than available in the history.

.. cmd:: BackTo num.
~~~~~~~~~~~~~~~~~



This command brings back the system to the state labeled `num`,
forgetting the effect of all commands executed after this state. The
state label is an integer which grows after each successful command.
It is displayed in the prompt when in -emacs mode. Just as `Back` (see
above), the `BackTo` command now handles proof states. For that, it may
have to undo some extra commands and end on a state `num′ ≤ num` if
necessary.


Variants:


.. cmdv:: Backtrack @num1 @num2 @num3 .

`Backtrack` is a *deprecated* form of
`BackTo` which allows explicitly manipulating the proof environment. The
three numbers num 1 , num 2 and num 3 represent the following:

    + `num3` : Number of Abort to perform, i.e. the number of currently
      opened nested proofs that must be canceled (see Chapter :ref:`TODO-7-proof-handling`_).
    + `num2` : *Proof state number* to unbury once aborts have been done.
      Coq will compute the number of Undo to perform (see Chapter :ref:`TODO-7-proof-handling`_).
    + `num1` : State label to reach, as for BackTo.




Error messages:


.. exn:: Invalid backtrack


The destination state label is unknown.


.. _quitting-and-debugging:

Quitting and debugging
--------------------------


.. cmd:: Quit.
~~~~~~~~~~~

This command permits to quit Coq.


.. cmd:: Drop.
~~~~~~~~~~~

This is used mostly as a debug facility by Coq’s implementors and does
not concern the casual user. This command permits to leave Coq
temporarily and enter theObjective Caml toplevel. The Objective Caml
command:


::

    #use "include";;


adds the right loadpaths and loads some toplevel printers for all
abstract types of Coq- section_path, identifiers, terms, judgments, ….
You can also use the file base_include instead, that loads only the
pretty-printers for section_paths and identifiers. You can return back
to Coq with the command:


::

    go();;



Warnings:


#. It only works with the bytecode version of Coq (i.e. coqtop called
   with option -byte, see the contents of Section `TODO-14.1-interactive-use`_).
#. You must have compiled Coq from the source package and set the
   environment variable COQTOP to the root of your copy of the sources
   (see Section `14.3.2-customization-by-envionment-variables`_).



.. cmd:: Time @command.
~~~~~~~~~~~~~~~~~~~

This command executes the vernacular command `command` and displays the
time needed to execute it.


.. cmd:: Redirect "file" @command.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command executes the vernacular command `command`, redirecting its
output to "`file`.out".


.. cmd:: Timeout @int @command.
~~~~~~~~~~~~~~~~~~~~~~~~~~

This command executes the vernacular command @command. If the command
has not terminated after the time specified by the integer (time
expressed in seconds), then it is interrupted and an error message is
displayed.


.. cmd:: Set Default Timeout @int.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

After using this command, all subsequent commands behave as if they
were passed to a Timeout command. Commands already starting by a
`Timeout` are unaffected.


.. cmd:: Unset Default Timeout.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command turns off the use of a default timeout.


.. cmd:: Test Default Timeout.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays whether some default timeout has be set or not.


.. _controlling-display:

Controlling display
-----------------------


.. cmd:: Set Silent.
~~~~~~~~~~~~~~~~~

This command turns off the normal displaying.


.. cmd:: Unset Silent.
~~~~~~~~~~~~~~~~~~~

This command turns the normal display on.


.. cmd:: Set Warnings ‘‘(@w1 ,…, @wn )’’.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command configures the display of warnings. It is experimental,
and expects, between quotes, a comma-separated list of warning names
or categories. Adding - in front of a warning or category disables it,
adding + makes it an error. It is possible to use the special
categories all and default, the latter containing the warnings enabled
by default. The flags are interpreted from left to right, so in case
of an overlap, the flags on the right have higher priority, meaning
that `A,-A` is equivalent to `-A`.


.. cmd:: Set Search Output Name Only.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command restricts the output of search commands to identifier
names; turning it on causes invocations of `Search`, `SearchHead`,
`SearchPattern`, `SearchRewrite` etc. to omit types from their output,
printing only identifiers.


.. cmd:: Unset Search Output Name Only.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command turns type display in search results back on.


.. cmd:: Set Printing Width @integer.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command sets which left-aligned part of the width of the screen
is used for display.


.. cmd:: Unset Printing Width.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the width of the screen used for display to its
default value (which is 78 at the time of writing this documentation).


.. cmd:: Test Printing Width.
~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current screen width used for display.


.. cmd:: Set Printing Depth @integer.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command sets the nesting depth of the formatter used for pretty-
printing. Beyond this depth, display of subterms is replaced by dots.


.. cmd:: Unset Printing Depth.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the nesting depth of the formatter used for
pretty-printing to its default value (at the time of writing this
documentation, the default value is 50).


.. cmd:: Test Printing Depth.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current nesting depth used for display.


.. cmd:: Unset Printing Compact Contexts.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the displaying of goals contexts to non compact
mode (default at the time of writing this documentation). Non compact
means that consecutive variables of different types are printed on
different lines.


.. cmd:: Set Printing Compact Contexts.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command sets the displaying of goals contexts to compact mode.
The printer tries to reduce the vertical size of goals contexts by
putting several variables (even if of different types) on the same
line provided it does not exceed the printing width (See Set Printing
Width above).


.. cmd:: Test Printing Compact Contexts.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current state of compaction of goal.


.. cmd:: Unset Printing Unfocused.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the displaying of goals to focused goals only
(default). Unfocused goals are created by focusing other goals with
bullets (see :ref:`TODO-7.2.7-bullets`_) or curly braces (see `7.2.6-curly-braces`_).


.. cmd:: Set Printing Unfocused.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command enables the displaying of unfocused goals. The goals are
displayed after the focused ones and are distinguished by a separator.


.. cmd:: Test Printing Unfocused.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current state of unfocused goals display.


.. cmd:: Set Printing Dependent Evars Line.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command enables the printing of the “(dependent evars: …)” line
when -emacs is passed.


.. cmd:: Unset Printing Dependent Evars Line.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command disables the printing of the “(dependent evars: …)” line
when -emacs is passed.


Controlling the reduction strategies and the conversion algorithm
----------------------------------------------------------------------


Coq provides reduction strategies that the tactics can invoke and two
different algorithms to check the convertibility of types. The first
conversion algorithm lazily compares applicative terms while the other
is a brute-force but efficient algorithm that first normalizes the
terms before comparing them. The second algorithm is based on a
bytecode representation of terms similar to the bytecode
representation used in the ZINC virtual machine [`98`_]. It is
especially useful for intensive computation of algebraic values, such
as numbers, and for reflection-based tactics. The commands to fine-
tune the reduction strategies and the lazy conversion algorithm are
described first.


.. cmd:: Opaque @qualid1 … @qualidn .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command has an effect on unfoldable constants, i.e. on constants
defined by ``Definition`` or ``Let`` (with an explicit body), or by a command
assimilated to a definition such as ``Fixpoint``, ``Program Definition``, etc,
or by a proof ended by ``Defined``. The command tells not to unfold the
constants `qualid1` … `qualidn` in tactics using δ-conversion (unfolding
a constant is replacing it by its definition).

``Opaque`` has also an effect on the conversion algorithm of Coq, telling
it to delay the unfolding of a constant as much as possible when Coq
has to check the conversion (see Section `TODO-4.3-conversion-rules`_) of two distinct
applied constants.

The scope of `Opaque` is limited to the current section, or current
file, unless the variant ``Global Opaque` `qualid1` … `qualidn` is used.


See also: sections :ref:`TODO-8.7-performing-computations`_, :ref:`TODO-8.16-automatizing`_, :ref:`TODO-7.1-switching-on-off-proof-editing-mode`_


Error messages:


.. exn:: The reference qualid was not found in the current environment

 There is no constant referred by qualid in the environment. Nevertheless, if
you asked Opaque foo bar and if bar does not exist, foo is set opaque.



.. cmd:: Transparent @qualid1 … @qualidn .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command is the converse of `Opaque`` and it applies on unfoldable
constants to restore their unfoldability after an Opaque command.

Note in particular that constants defined by a proof ended by Qed are
not unfoldable and Transparent has no effect on them. This is to keep
with the usual mathematical practice of *proof irrelevance*: what
matters in a mathematical development is the sequence of lemma
statements, not their actual proofs. This distinguishes lemmas from
the usual defined constants, whose actual values are of course
relevant in general.

The scope of Transparent is limited to the current section, or current
file, unless the variant ``Global Transparent`` `qualid1` … `qualidn` is
used.


Error messages:


.. exn:: The reference @qualid was not found in the current environment

There is no constant referred by `qualid` in the environment.



See also: sections :ref:`TODO-8.7-performing-computations`_, :ref:`TODO-8.16-automatizing`_, :ref:`TODO-7.1-switching-on-off-proof-editing-mode`_


.. cmd:: Strategy @level [ @qualid1 … @qualidn ].
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command generalizes the behavior of Opaque and Transparent
commands. It is used to fine-tune the strategy for unfolding
constants, both at the tactic level and at the kernel level. This
command associates a level to `qualid1` … `qualidn` . Whenever two
expressions with two distinct head constants are compared (for
instance, this comparison can be triggered by a type cast), the one
with lower level is expanded first. In case of a tie, the second one
(appearing in the cast type) is expanded.

Levels can be one of the following (higher to lower):

:opaque : level of opaque constants. They cannot be expanded by
  tactics (behaves like +∞, see next item).
:num : levels indexed by an integer. Level 0 corresponds to the
  default behavior, which corresponds to transparent constants. This
  level can also be referred to as transparent. Negative levels
  correspond to constants to be expanded before normal transparent
  constants, while positive levels correspond to constants to be
  expanded after normal transparent constants.
:expand : level of constants that should be expanded first (behaves
  like −∞)


These directives survive section and module closure, unless the
command is prefixed by Local. In the latter case, the behavior
regarding sections and modules is the same as for the ``Transparent`` and
``Opaque`` commands.


.. cmd:: Print Strategy @qualid.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command prints the strategy currently associated to `qualid`. It
fails if `qualid` is not an unfoldable reference, that is, neither a
variable nor a constant.


Error messages:


.. exn:: The reference is not unfoldable.



Variants:


.. cmdv:: Print Strategies.

Print all the currently non-transparent strategies.



.. cmd:: Declare Reduction @ident := @convtactic.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command allows giving a short name to a reduction expression, for
instance lazy beta delta [foo bar]. This short name can then be used
in ``Eval ident in`` ... or ``eval`` directives. This command accepts the
Local modifier, for discarding this reduction name at the end of the
file or module. For the moment the name cannot be qualified. In
particular declaring the same name in several modules or in several
functor applications will be refused if these declarations are not
local. The name `ident` cannot be used directly as an Ltac tactic, but
nothing prevents the user to also perform a
``Ltac`` `ident` ``:=`` `convtactic`.


See also: sections :ref:`TODO-8.7-performing-computations`_


.. _controlling-locality-of-commands:

Controlling the locality of commands
-----------------------------------------


.. cmd:: Local @command.
.. cmd::  Global @command.
~~~~~~~~~~~~~~~~~~~~

Some commands support a Local or Global prefix modifier to control the
scope of their effect. There are four kinds of commands:


+ Commands whose default is to extend their effect both outside the
  section and the module or library file they occur in.  For these
  commands, the Local modifier limits the effect of the command to the
  current section or module it occurs in.  As an example, the ``Coercion``
  (see Section :ref:`TODO-2.8-coercions`_) and ``Strategy`` (see Section :ref:`TODO-6.10.3-strategy`_) commands belong
  to this category.
+ Commands whose default behavior is to stop their effect at the end
  of the section they occur in but to extent their effect outside the
  module or library file they occur in.  For these commands, the Local
  modifier limits the effect of the command to the current module if the
  command does not occur in a section and the Global modifier extends
  the effect outside the current sections and current module if the
  command occurs in a section.  As an example, the ``Implicit Arguments`` (see
  Section :ref:`TODO-2.7-implicit-arguments`_), Ltac (see Chapter :ref:`TODO-9-tactic-language`_) or ``Notation`` (see Section
  :ref:`TODO-12.1-notations`_) commands belong to this category.  Notice that a subclass of
  these commands do not support extension of their scope outside
  sections at all and the Global is not applicable to them.
+ Commands whose default behavior is to stop their effect at the end
  of the section or module they occur in.  For these commands, the Global
  modifier extends their effect outside the sections and modules they
  occurs in.  The ``Transparent`` and ``Opaque`` (see Section :ref:`TODO-6.10-opaque`_) commands  belong to this category.
+ Commands whose default behavior is to extend their effect outside
  sections but not outside modules when they occur in a section and to
  extend their effect outside the module or library file they occur in
  when no section contains them.For these commands, the Local modifier
  limits the effect to the current section or module while the Global
  modifier extends the effect outside the module even when the command
  occurs in a section.  The ``Set`` and ``Unset`` commands belong to this
  category.


Navigation
----------


+ `Cover`_
+ `Table of contents`_
+ Index

    + `General`_
    + `Commands`_
    + `Options`_
    + `Tactics`_
    + `Errors`_




+ `webmaster`_
+ `xhtml valid`_
+ `CSS valid`_


.. _2.9: :///home/steck/gallina-ext.html#SetPrintingAll
.. _Get Coq: :///download
.. _6.11  Controlling the locality of commands: :///home/steck/vernacular.html#sec317
.. _About Coq: :///about-coq
.. _6.5  Compiled files: :///home/steck/vernacular.html#compiled
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _7.2.6: :///home/steck/proof-handling.html#curlybacket
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _14.3.2: :///home/steck/commands.html#EnvVariables
.. _4.3: :///home/steck/cic.html#conv-rules
.. _6.8  Quitting and debugging: :///home/steck/vernacular.html#sec282
.. _14.1: :///home/steck/commands.html#binary-images
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _8.1: :///home/steck/tactics.html#tactic-syntax
.. _6.7  Backtracking: :///home/steck/vernacular.html#sec278
.. _23: :///home/steck/extraction.html#Extraction
.. _12.1.10: :///home/steck/syntax-extensions.html#LocateSymbol
.. _6.9  Controlling display: :///home/steck/vernacular.html#sec291
.. _6.10  Controlling the reduction strategies and the conversion algorithm: :///home/steck/vernacular.html#sec311
.. _6.4  Loading files: :///home/steck/vernacular.html#sec259
.. _6.2  Flags, Options and Tables: :///home/steck/vernacular.html#sec238
.. _Options: :///home/steck/option-index.html
.. _6.1  Displaying: :///home/steck/vernacular.html#sec235
.. _webmaster: mailto:coq-www_@_inria.fr
.. _Commands: :///home/steck/command-index.html
.. _7.2.7: :///home/steck/proof-handling.html#bullets
.. _2.7: :///home/steck/gallina-ext.html#Implicit%20Arguments
.. _8.16: :///home/steck/tactics.html#Automatizing
.. _12.2.2: :///home/steck/syntax-extensions.html#scopechange
.. _4.1.1: :///home/steck/cic.html#Sorts
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _7: :///home/steck/proof-handling.html#Proof-handling
.. _7.1: :///home/steck/proof-handling.html#Theorem
.. _9: :///home/steck/ltac.html#TacticLanguage
.. _6.6  Loadpath: :///home/steck/vernacular.html#sec266
.. _General: :///home/steck/general-index.html
.. _14: :///home/steck/commands.html#Addoc-coqc
.. _2.5.8: :///home/steck/gallina-ext.html#Import
.. _8.7: :///home/steck/tactics.html#Conversion-tactics
.. _The Coq Proof Assistant: :///
.. _2.2.4: :///home/steck/gallina-ext.html#AddPrintingLet
.. _Documentation: :///documentation
.. _2.8: :///home/steck/gallina-ext.html#Coercions
.. _12.1: :///home/steck/syntax-extensions.html#Notation
.. _98: :///home/steck/biblio.html#Leroy90
.. _6.3  Requests to the environment: :///home/steck/vernacular.html#sec247
.. _2.6.3: :///home/steck/gallina-ext.html#loadpath
