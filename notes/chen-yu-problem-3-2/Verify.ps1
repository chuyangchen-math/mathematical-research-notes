param()
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
$oldThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_NUM_THREADS = '1'
    foreach ($record in (Import-Csv -LiteralPath 'logs/current/modules.csv')) {
        if (Test-Path -LiteralPath ('.lake/build/lib/lean/' + $record.Module + '.olean')) { continue }
        & lake build $record.Module
        if ($LASTEXITCODE -ne 0) { throw "Lean build failed at $($record.Module)." }
    }
    & lake build
    if ($LASTEXITCODE -ne 0) { throw 'Full project and dependency validation failed.' }
    $audit = & lake env lean Main.lean 2>&1
    $audit | Write-Output
    if ($LASTEXITCODE -ne 0) { throw 'Entry-point audit failed.' }
    if (($audit -join "`n") -match 'sorryAx') { throw 'Unproved declaration in audit.' }
} finally {
    $env:LEAN_NUM_THREADS = $oldThreads
    Pop-Location
}
