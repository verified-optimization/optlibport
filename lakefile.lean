import Lake
open Lake DSL System

-- Usually the `tag` will be of the form `nightly-2021-11-22`.
-- If you would like to use an artifact from a PR build,
-- it will be of the form `pr-branchname-sha`.
def tag : String := "port-2022-10-06-9726f59"
def releaseRepo : String := "verified-optimization/mathport-optlib"
def oleanTarName : String := "optlib-binport.tar.gz"

def download (url : String) (to : FilePath) : BuildM PUnit := Lake.proc
{ -- We use `curl -O` to ensure we clobber any existing file.
  cmd := "curl",
  args := #["-L", "-O", url]
  cwd := to }

def untar (file : FilePath) : BuildM PUnit := Lake.proc
{ cmd := "tar",
  args := #["-xzf", file.fileName.getD "."] -- really should throw an error if `file.fileName = none`
  cwd := file.parent }

def getReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit :=
download s!"https://github.com/{repo}/releases/download/{tag}/{artifact}" to

def untarReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit := do
  getReleaseArtifact repo tag artifact to
  untar (to / artifact)

package optlibport where
  extraDepTargets := #[`fetchOleans]

target fetchOleans (_pkg : Package) : Unit := do
  let libDir : FilePath := __dir__ / "build" / "lib"
  IO.FS.createDirAll libDir
  let oldTrace := Hash.ofString tag
  let _ ← buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
    logInfo "Fetching oleans for Mathbin"
    untarReleaseArtifact releaseRepo tag oleanTarName libDir
  return .nil

require mathlib3port from git "https://github.com/leanprover-community/mathlib3port.git"@"0ef9b6d2572e49c015c955be6c551ba5d6894fe6"

lean_lib Optbin where
  roots := #[]
  globs := #[`Optbin]
