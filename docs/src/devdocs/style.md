# Style Guide for AlgebraicJulia

The purpose of this document is to have a consistent style across AlgebraicJulia, for interests of maintainability and professionalism.

## Folder structure

We follow the Julia project folder structure, where the most important elements are

- A `Project.toml` file, describing dependencies and metadata.
- A `src` directory. Most functionality should be implemented in this directory.
- A `test` directory. Functionality implemented in `src` should be tested here.
- A `README.md`. This should describe the purpose of the project.

Additional directories one might also use

- A `notebooks` directory for explanatory notebooks.
- A `docs` directory with `Documenter.jl`-generated docs.
- A `scripts` directory with executable scripts. Note: these scripts should not contain many functions or types, they should be thin wrappers around functions from `src`. It is acceptable to develop some functionality in a script if that functionality is eventually migrated into `src`.

For most repositories in AlgebraicJulia, this should describe the top-level structure. However, some repositories might be multi-project. In that case, there is a top-level directory consisting of project directories, some of which may depend on each other.

## Naming conventions

There are two ways of joining words together without spaces that are in use across AlgebraicJulia.

1. UpperCamelCase, in which each word is capitalized, and then joined together without a separating character.

2. lower\_snake\_case, in which each word is lowercase, and then joined together with underscores. The use of uppercase acronyms in lower\_snake\_case is tolerable but discouraged.

Occasionally, it is also acceptable to join lowercase words together without underscores, e.g., `setindex!` instead of `set_index!`; judgement about readability and consistency should be used when making the decision to use underscores or not.

Here are some example of names that are **not** consistent with the AlgebraicJulia style.

- `camelCase`
- `UpperCamel_and_snake`
- `Dashed-name`

### Projects

Projects should be named using UpperCamelCase with a `.jl` suffix, e.g. AlgebraicPetri.jl or Semagrams.jl.

### Files and directories

Directories should all be lower\_snake\_case, except for top-level directories that are named after projects.

Library julia files and test julia files should be named with UpperCamelCase. Scripts and notebooks should be lower\_snake\_case.

### Julia values

Modules and types should always be UpperCamelCase. Functions should always be lower\_snake\_case, and ideally single words. Constants should be lower\_snake\_case, or occasionally `SCREAMING_SNAKE_CASE` (judgement should be exercised about use of `SCREAMING_SNAKE_CASE`). Fields of structs should be lower\_snake\_case, or ideally lowercase single words.

Arguments to functions should have short names, often just single letters. If your function is so specific that the arguments need to be described with long argument names, consider generalizing your function. If arguments need to be longer, then lower\_snake\_case should be used. Additionally, you can use types and comments to document what a variable is for instead of making the names long. Some examples:

```julia
f(a_natural_number) # BAD
f(n::Nat) # GOOD
f(graph, vector_of_weights) # BAD
f(g::AbstractGraph, v::AbstractVector) # GOOD
```

## General style tips

See the official [Julia style guide](https://docs.julialang.org/en/v1/manual/style-guide/) for general guidelines but note the following additions and exceptions:

- Indent width is **2 spaces**. For VSCode, go to settings and set `Editor: Tab Size` to 2.
- Try to avoid lines longer than **80 characters**. Occasionally it may be convenient to go over slightly, but never do so egregiously. To hard wrap docstrings in VSCode, the extension [Rewrap](https://marketplace.visualstudio.com/items?itemName=stkb.rewrap) adds the keybinding `Alt+Q` (as in Emacs).
- Introduce a new struct when many (≥3) functions have overlapping arguments that are common aspects of a shared concept
- Catlab uses modules more often than most Julia packages. While this may be idiosyncratic, it helps keep different components of Catlab isolated, which will be useful in the future when we spin out modules as their own packages.
- Prefer accessor and mutator functions (e.g. `dom(f)`) over direct manipulation of struct fields or keys (e.g. `f.dom`), especially when the functions already exist. This convention supports writing generic code and makes it easier to change data structure internals without breaking existing code.
- In long files, using comment headers can improve readability and navigability. Top-level headers and sub-headers should be formatted as:

```julia
# Section
#########

# Subsection
#-----------
```

## Guidelines for pull requests

Every pull request to Catlab should be reviewed by at least one person. Following are some things to check when making a PR yourself or reviewing someone else's PR. The goal of this list is to ensure that the Catlab codebase is robust and maintainable. When any of these guidelines are violated, it should be documented in a comment on the PR page.

**Note**: This list only includes the mechanical things. When a reviewing a PR you should always use your own judgment in asking questions and making comments about API and algorithm design. That's the hard part!

### Tests and code coverage

- Enhancements (new features) must have accompanying unit tests
- Bug fixes should come with unit tests exposing the bug, unless producing a minimal example is unusually difficult
- Do not delete existing unit tests, unless you have a very good reason (e.g., the relevant functionality is being moved to another package), which is documented in the PR
- If you are adding a new module, make sure to add the test module to the test runner (`test/runtests.jl` or file included therein)
- Code coverage on the Catlab repo exceeds 90% and we try to keep it that way. We do not insist on 100% coverage, which is impractical, nor do we set a hard threshold applicable to all PRs, but generally you should aim for 90%+ code coverage. Any reductions in test coverage should be justified in the PR.

### Documentation

- All exported functions, types, and constants must have docstrings
- Docstrings should be written in complete sentences, with correct capitalization and punctuation. Likewise for comments, except for fragmentary end-of-line comments.
- Where possible, provide citations for constructions and algorithms that you implement. This reflects good scholarly values and also aids the understanding of your code by other people.

### Version control

- Commit messages should be informative and be written in complete sentences
- Avoid one-word commit messages like "fix" or "bug". If you need to make very simple fixes on your branch, amend a previous commit and force push.
- Avoid repeatedly merging the master branch back into your PR branch. Instead, rebase off master and force push.

### Backwards compatibility

Reflecting Catlab's dual status as a research project and a user-facing library, we want to give ourselves space to experiment while also not annoying our users and each other by needlessly breaking things.

- Like other Julia packages, Catlab aims to follow [semantic versioning](https://pkgdocs.julialang.org/v1/compatibility/)
- All else equal, it is better to make breaking changes to new APIs, especially very new ones, than old APIs
- If you plan to make major breaking changes, please coordinate with the senior developers to ensure that it makes senses and aligns with the release schedule
