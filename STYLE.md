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

## Capitalization and multi-word conventions

There are two ways of joining words together without spaces that are in use across AlgebraicJulia.

The first way is UpperCamelCase. In UpperCamelCase, each word is capitalized, and then joined together without a separating character.

The second way is lower\_snake\_case. In lower\_snake\_case, each word is lowercase, and then joined together with underscores. The use of uppercase acronyms in lower\_snake\_case is tolerable, but not preferred.

Occasionally, it is also acceptable to join lowercase words together without underscores, i.e. `setindex!` instead of `set_index!`; judgement about readability and consistency should be used when making the decision to use underscores or not.

Here are some example of names that are not consistent with the AlgebraicJulia style.

- `camelCase`
- `UpperCamel_and_snake`
- `Dashed-name`

### Projects

Projects should be named using UpperCamelCase with a `.jl` suffix, i.e. AlgebraicPetri.jl, or Semagrams.jl.

### Files and directories

Directories should all be lower\_snake\_case, except for top-level directories that are named after projects.

Library julia files and test julia files should be named with UpperCamelCase. Scripts and notebooks should be lower\_snake\_case.

### Julia values

Modules and types should always be UpperCamelCase. Functions should always be lower\_snake\_case. Constants should be lower\_snake\_case, or occasionally `SCREAMING_SNAKE_CASE` (judgement should be exercised about use of `SCREAMING_SNAKE_CASE`).

Fields of structs should be lower\_snake\_case, or ideally lowercase single words.

Arguments to functions should ideally be single-letter. If your function is so specific that the arguments need to be described with long argument names, consider generalizing your function. If arguments need to be longer, then lower\_snake\_case should be used.

## Indentation

We indent with two spaces. Look up how to make your editor indent with two spaces.
