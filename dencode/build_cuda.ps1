param(
    [string]$Out = "dencoder_cuda.exe",
    [string]$CudaPath = ""
)

$ErrorActionPreference = "Stop"

function Get-ShortPath([string]$PathIn) {
    $p = (Resolve-Path -LiteralPath $PathIn).Path
    $short = cmd /c "for %I in (""$p"") do @echo %~sI"
    if ($LASTEXITCODE -ne 0 -or -not $short) {
        return $p
    }
    return $short.Trim()
}

if (-not $CudaPath -or $CudaPath.Trim() -eq "") {
    if ($env:CUDA_PATH -and (Test-Path $env:CUDA_PATH)) {
        $CudaPath = $env:CUDA_PATH
    } else {
        $roots = @( "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA" )
        foreach ($r in $roots) {
            if (Test-Path $r) {
                $dirs = Get-ChildItem -Path $r -Directory | Sort-Object Name -Descending
                if ($dirs.Count -gt 0) {
                    $CudaPath = $dirs[0].FullName
                    break
                }
            }
        }
    }
}

if (-not $CudaPath -or -not (Test-Path $CudaPath)) {
    throw "CUDA Toolkit not found. Install CUDA Toolkit or pass -CudaPath."
}

$inc = Join-Path $CudaPath "include"
$lib = Join-Path $CudaPath "lib\x64"
$bin = Join-Path $CudaPath "bin"
$binX64 = Join-Path $bin "x64"

if (-not (Test-Path (Join-Path $inc "cuda_runtime.h"))) {
    throw "Missing header: $inc\cuda_runtime.h"
}
$dllDir = $bin
if (Test-Path $binX64) {
    $dllDir = $binX64
}

$cudartDll = Get-ChildItem -Path $dllDir -Filter "cudart64_*.dll" -ErrorAction SilentlyContinue | Sort-Object Name -Descending | Select-Object -First 1
if (-not $cudartDll) {
    throw "Missing CUDA runtime DLL in $dllDir (expected cudart64_*.dll)"
}
$cublasDll = Get-ChildItem -Path $dllDir -Filter "cublas64_*.dll" -ErrorAction SilentlyContinue | Sort-Object Name -Descending | Select-Object -First 1
if (-not $cublasDll) {
    throw "Missing cuBLAS DLL in $dllDir (expected cublas64_*.dll)"
}
$nvrtcDll = Get-ChildItem -Path $dllDir -Filter "nvrtc64_*.dll" -ErrorAction SilentlyContinue | Sort-Object Name -Descending | Select-Object -First 1
if (-not $nvrtcDll) {
    throw "Missing NVRTC DLL in $dllDir (expected nvrtc64_*.dll)"
}

$incShort = Get-ShortPath $inc
$binShort = Get-ShortPath $dllDir

$env:CGO_ENABLED = "1"
$env:CGO_CFLAGS = "-I$incShort"
$env:CGO_CXXFLAGS = "-I$incShort"
$env:CGO_LDFLAGS = "-L$binShort -Wl,-Bdynamic -l:$($cudartDll.Name) -l:$($cublasDll.Name) -l:$($nvrtcDll.Name)"
$env:PATH = "$dllDir;$env:PATH"

Write-Host "[*] CUDA path: $CudaPath"
Write-Host "[*] CUDA DLL dir: $dllDir"
Write-Host "[*] CUDA DLLs: $($cudartDll.Name), $($cublasDll.Name), $($nvrtcDll.Name)"
Write-Host "[*] Building with tags: cuda"
go build -tags cuda -o $Out .
if ($LASTEXITCODE -ne 0) {
    throw "go build failed with exit code $LASTEXITCODE"
}
Write-Host "[+] Built: $Out"
