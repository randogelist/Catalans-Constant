@echo off
setlocal EnableExtensions EnableDelayedExpansion
cd /d "%~dp0"
echo PACKAGE=CATALAN_CLOSURE_REDUCTION_v0_2_0
echo RUNNER=NATIVE_WINDOWS_LEAN_433
echo NETWORK=NOT_USED
echo LAKE=NOT_USED
echo PYTHON=NOT_USED
echo POWERSHELL=NOT_USED
echo WSL=NOT_USED
echo NATIVE_DECIDE=NOT_USED
set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if defined ZETA3_LEAN_EXE set "LEAN_EXE=!ZETA3_LEAN_EXE!"
if defined CATALAN_LEAN_EXE set "LEAN_EXE=!CATALAN_LEAN_EXE!"
if not exist "!LEAN_EXE!" (
  echo LEAN_COMPILER=NOT_FOUND
  echo Set CATALAN_LEAN_EXE to the full path of your Lean 4.33.0 lean.exe.
  exit /b 2
)
if not exist "logs" mkdir "logs"
"!LEAN_EXE!" --version > "logs\00_version.txt" 2>&1
if errorlevel 1 (
  type "logs\00_version.txt"
  exit /b 2
)
type "logs\00_version.txt"
findstr /C:"version 4.33.0," "logs\00_version.txt" >nul
if errorlevel 1 (
  echo LEAN_VERSION=EXPECTED_4_33_0
  exit /b 2
)
set "CACHE_ROOT=%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
if defined ZETA3_CACHE_ROOT set "CACHE_ROOT=!ZETA3_CACHE_ROOT!"
if defined CATALAN_CACHE_ROOT set "CACHE_ROOT=!CATALAN_CACHE_ROOT!"
set "OLD_LEAN_PATH=!LEAN_PATH!"
set "LEAN_PATH=%CD%\build"
for %%R in ("!CACHE_ROOT!\.lake\build\lib\lean" "!CACHE_ROOT!\build\lib\lean" "!CACHE_ROOT!\lib\lean") do (
  if exist "%%~fR" set "LEAN_PATH=!LEAN_PATH!;%%~fR"
)
for /d %%P in ("!CACHE_ROOT!\.lake\packages\*") do (
  if exist "%%~fP\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%%~fP\.lake\build\lib\lean"
)
if defined OLD_LEAN_PATH set "LEAN_PATH=!LEAN_PATH!;!OLD_LEAN_PATH!"
set "HURWITZ_CACHE=NOT_FOUND"
for %%R in ("!LEAN_PATH:;=" "!") do (
  if exist "%%~R\Mathlib\NumberTheory\LSeries\HurwitzZeta.olean" set "HURWITZ_CACHE=READY"
)
echo CACHE_ROOT=!CACHE_ROOT!
echo HURWITZ_CACHE=!HURWITZ_CACHE!
if "!HURWITZ_CACHE!"=="NOT_FOUND" (
  echo Set CATALAN_CACHE_ROOT to the project containing your existing Mathlib cache.
  exit /b 3
)
set "LEAN_THREADS=2"
if defined CATALAN_LEAN_THREADS set "LEAN_THREADS=!CATALAN_LEAN_THREADS!"
echo LEAN_THREADS=!LEAN_THREADS!
if not exist "build\CatalanAnchor" mkdir "build\CatalanAnchor"
if not exist "build\GPBKQRXY" mkdir "build\GPBKQRXY"
findstr /S /N /R /C:"^[ ]*axiom " /C:"^[ ]*constant " /C:"\<sorry\>" /C:"\<admit\>" /C:"native_decide" "CatalanAnchor\*.lean" "GPBKQRXY\*.lean" "CatalanAnchor.lean" "Main.lean" > "logs\01_source_scan.txt"
set "SOURCE_SCAN_EXIT=!errorlevel!"
if !SOURCE_SCAN_EXIT! GEQ 2 (
  type "logs\01_source_scan.txt"
  echo SOURCE_TRUST_SCAN=SCAN_ERROR
  exit /b 4
)
if "!SOURCE_SCAN_EXIT!"=="0" (
  type "logs\01_source_scan.txt"
  echo SOURCE_TRUST_SCAN=FAIL
  exit /b 4
)
echo SOURCE_TRUST_SCAN=PASS
call :compile CatalanAnchor\Series 02_series
if errorlevel 1 exit /b 5
call :compile CatalanAnchor\HurwitzBridge 03_hurwitz
if errorlevel 1 exit /b 6
call :compile CatalanAnchor\Bounds 04_bounds
if errorlevel 1 exit /b 7
call :compile CatalanAnchor\Scoping 05_scoping
if errorlevel 1 exit /b 8
call :compile CatalanAnchor\Integral 06_integral
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\FiniteCertificate 06_finite_certificate
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\IntervalScope new_intervalscope
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\Certificate1000 new_certificate1000
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\EulerKernel new_eulerkernel
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\EulerAnalytic new_euleranalytic
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\EulerFixedPoint new_eulerfixedpoint
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\EulerComputed new_eulercomputed
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\ScopeReplay new_scopereplay
if errorlevel 1 exit /b 9
call :compile GPBKQRXY\RieszCore admission_0
if errorlevel 1 exit /b 9
call :compile GPBKQRXY\RieszRepresentative admission_1
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\EulerUniform admission_2
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\Admission admission_3
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\AdmissionClosure admission_4
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\AdmissionPrecision admission_5
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\CofinalClosure closure_cofinal
if errorlevel 1 exit /b 9
call :compile CatalanAnchor\ArithmeticClosure closure_arithmetic
if errorlevel 1 exit /b 9
call :compile CatalanAnchor 07_root
if errorlevel 1 exit /b 10
call :compile Main 08_main
if errorlevel 1 exit /b 11
"!LEAN_EXE!" -j !LEAN_THREADS! "CatalanAnchor\Audit.lean" > "logs\09_axiom_audit.txt" 2>&1
if errorlevel 1 (
  type "logs\09_axiom_audit.txt"
  echo AXIOM_AUDIT=FAIL
  exit /b 12
)
type "logs\09_axiom_audit.txt"
findstr /I /C:"sorryAx" /C:"ofReduceBool" /C:"Lean.trustCompiler" /C:"Lean.ofReduceNat" "logs\09_axiom_audit.txt" >nul
set "AXIOM_SCAN_EXIT=!errorlevel!"
if !AXIOM_SCAN_EXIT! GEQ 2 (
  echo AXIOM_AUDIT=SCAN_ERROR
  exit /b 13
)
if "!AXIOM_SCAN_EXIT!"=="0" (
  echo AXIOM_AUDIT=NONSTANDARD
  exit /b 13
)
echo AXIOM_AUDIT=PASS
echo CATALAN_SERIES_CONVERGENCE=PROVED
echo CATALAN_HURWITZ_IDENTIFICATION=PROVED
echo CATALAN_RATIONAL_BOUNDS=PROVED
echo CATALAN_DOUBLE_INTEGRAL_IDENTIFICATION=PROVED
echo FINITE_DENOMINATOR_SCOPE=PROVED
echo NATIVE_CATALAN_FINITE_SCOPE_TEN=PROVED
echo EULER_ANALYTIC_ENCLOSURE=PROVED
echo EULER_FIXED_POINT_ROUNDING=PROVED
echo EXACT_1000_PLACE_INTERVAL=PROVED
echo CATALAN_FINITE_SCOPE_501_DIGIT_BOUND=PROVED
echo NATIVE_CATALAN_FINITE_SCOPE_10_POW_500=PROVED
echo UNIFORM_EULER_ENCLOSURE=PROVED
echo CATALAN_COORDINATE_DATA=ENCODED
echo CATALAN_LOCAL_COORDINATE_ADMISSION=PROVED
echo CATALAN_UNIVERSAL_LINEAR_LAWS=PROVED
echo CATALAN_IRRATIONALITY_FROM_SUCCESSOR=PROVED_CONDITIONALLY
echo BOUNDED_PRECISION_LOCK_OBSTRUCTION=PROVED
echo IDENTITY_SEED_ADMISSION=PROVED
echo IDENTITY_SUCCESSOR_NOT_LOCK=PROVED
echo SUCCESSOR_IFF_COFINAL_ADMISSION=PROVED
echo SUCCESSOR_IFF_ARITHMETIC_EXHAUSTION=PROVED
echo LOCK_IFF_ARITHMETIC_EXHAUSTION=PROVED
echo INTEGER_CHECK_NATIVE_CATALAN_SOUNDNESS=PROVED
echo SEED_COVERS_ALL_SMALLER_POSITIVE_SCOPES=PROVED
echo ARITHMETIC_EXHAUSTION=NOT_PROVED
echo SUCCESSOR_FROM_EXHAUSTION=PROVED_CONDITIONALLY
echo RIESZ_LOCK=NOT_CONSTRUCTED
echo CATALAN_SUCCESSOR_PRESERVATION=EXPLICIT_INPUT
echo CATALAN_SCOPE_DOUBLING=EXPLICIT_INPUT
echo CATALAN_IRRATIONALITY_ENDPOINT=CONDITIONAL_ON_SUCCESSOR
echo CATALAN_INFINITE_WITNESS=NOT_CONSTRUCTED
echo UNCONDITIONAL_CATALAN_IRRATIONALITY=NOT_CLAIMED
echo PACKAGE_BUILD=PASS
exit /b 0

:compile
echo COMPILE=%~1.lean
"!LEAN_EXE!" -j !LEAN_THREADS! -o "build\%~1.olean" "%~1.lean" > "logs\%~2.txt" 2>&1
if errorlevel 1 (
  type "logs\%~2.txt"
  echo COMPILE_RESULT=FAIL
  exit /b 1
)
type "logs\%~2.txt"
echo COMPILE_RESULT=PASS
exit /b 0
