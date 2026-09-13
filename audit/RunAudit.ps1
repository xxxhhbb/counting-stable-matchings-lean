$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $PSScriptRoot
$leanRoot = Join-Path $repoRoot "lean_e2e"
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
if ($lakeCommand) {
    $lake = $lakeCommand.Source
}
else {
    $pinnedLake = Join-Path $env:USERPROFILE `
        ".elan\toolchains\leanprover--lean4---v4.32.2\bin\lake.exe"
    if (-not (Test-Path -LiteralPath $pinnedLake)) {
        throw "Lake was not found. Install Lean through elan or add lake to PATH."
    }
    $lake = $pinnedLake
}

Push-Location $leanRoot
try {
    & $lake build
    if ($LASTEXITCODE -ne 0) { throw "lake build failed" }

    & $lake env lean (Join-Path $PSScriptRoot "StablePairAxiomAudit.lean")
    if ($LASTEXITCODE -ne 0) { throw "stable-pair axiom audit failed" }

    & $lake env lean (Join-Path $PSScriptRoot "ParticipantCountAxiomAudit.lean")
    if ($LASTEXITCODE -ne 0) { throw "participant-count axiom audit failed" }

    & $lake env lean (Join-Path $PSScriptRoot "AllSizeEndpointAudit.lean")
    if ($LASTEXITCODE -ne 0) { throw "all-size endpoint audit failed" }

    & $lake env lean (Join-Path $PSScriptRoot "FinalKernelChecks.lean")
    if ($LASTEXITCODE -ne 0) { throw "kernel signature audit failed" }

    & $lake env lean (Join-Path $PSScriptRoot "MutationCounterexamples.lean")
    if ($LASTEXITCODE -ne 0) { throw "semantic mutation checks failed" }
}
finally {
    Pop-Location
}

$auditRoots = @(
    (Join-Path $repoRoot "lean"),
    (Join-Path $repoRoot "lean_random_reveal"),
    (Join-Path $repoRoot "lean_entropy"),
    (Join-Path $repoRoot "lean_probability"),
    (Join-Path $repoRoot "lean_e2e\StableMatchingsE2E"),
    (Join-Path $repoRoot "joint_charging"),
    (Join-Path $repoRoot "constant_optimization"),
    $PSScriptRoot
)

$forbiddenPattern = '^\s*(axiom|opaque)\b|\b(sorry|admit)\b|sorryAx|implemented_by'
$leanFiles = Get-ChildItem -LiteralPath $auditRoots -Recurse -File -Filter "*.lean"
$forbiddenHits = $leanFiles | Select-String -Pattern $forbiddenPattern
if ($forbiddenHits) {
    $forbiddenHits | ForEach-Object {
        Write-Error ("{0}:{1}:{2}" -f $_.Path, $_.LineNumber, $_.Line)
    }
    throw "forbidden Lean token found"
}

$lineCount = (($leanFiles | Get-Content | Measure-Object -Line).Lines)
Write-Output ("FORBIDDEN_TOKEN_SCAN_PASS ({0} files, {1} lines)" -f `
    $leanFiles.Count, $lineCount)
Write-Output "COUNTING_STABLE_MATCHINGS_LEAN_AUDIT_PASS"
