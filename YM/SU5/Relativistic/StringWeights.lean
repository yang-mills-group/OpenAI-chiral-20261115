import YM.SU5.Relativistic.StringSignal
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P₀" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history

variable {s n:ℕ}
local notation "μ" z:max=> gaugeShift Λ.block z
local notation "E₀" s:max f:max=> Lariat.rideL Y H T s f


open Lariat
section weights
variable (M:Panel Y H D.univ_ G.history G.clipped d false (c d)) (y:M.X)

variable (A:∀ i:ℕ, Future Y H d i)(w:ℕ→ℕ) (p: Subscribed Y H D G d c M y u T A w)
open Lariat
local notation "I₁" i:max=>a (G.rows (u (w i)))
local notation "K₁" i:max=>b (G.columns (u (w i)))
local notation "F₀" i:max=> (Future.kernelPath Y H d (A i)).val
local notation "Y'" i:max=>(A i).t
local notation "Φ" i:max=> sharp Y H (Y' i) (I₁ i) (K₁ i) (Future.kernelPath Y H d (A i)).val
local notation "R₀" s:max=>appeal Y H D G d c (M.character y) T s

private lemma respan_holds (i k s r:ℕ)(p:Tapestry.Pay Y (s+r) i k) : respan Y H s i k (padTop (start (quiet (tent Y H))) r)=1:=by
 induction r with
 | zero=> exact (distribute_arith Y H s i 1 1 1).2.2.2.1
 | succ n ih=>
    have he:s+n<Y.uv k:= p.2
    let a:= Lariat.padTop (Lariat.start (Lariat.quiet (tent Y H))) n
    have g:= ih ⟨p.1,he.le⟩
    rw [Lariat.padTop,Lariat.respan,g,show distribute Y H (s+(0+n)+1) i (quiet K).mark =1 from (distribute_arith Y H _ _ 1 1 1).2.2.2.1,mul_one,ascendUnit] -- Check zero base +n defeq
    exact ⟨p.1,(by simp; omega)⟩
include p t
lemma pieceSame: Tendsto (fun i=>Φ i) atTop (𝓝 1):=by
 let z:Lariat K 0:= start (quiet K)
 have hp:(R₀ 0) z=1:=by
    change (if false=true then (0:ℂ) else evaluate Y H V G d c (SameCharacter.resident Y H V G d false (c d) (M.character y)) 0 1)=1
    rw [if_neg Bool.false_ne_true]; exact (consistency Y H V G d c (SameCharacter.resident Y H V G d false (c d) (M.character y)) ∅ 0).unit
 have hx:= p.move 0 0 z; rw [hp] at hx; apply hx.congr'
 filter_upwards [p.calibrated 0 0 z] with i ⟨i',S,t₀,v₀,e₀⟩
 let U:=Lariat.parcel Y H d (A i) 0 z; let r:=(A i).t-1
 have hz: 0+(0+r+1)= (A i).t:=by unfold r; omega
 let v:=0+r+1
 let F:=priceAt Y H 0 (I₁ i) (K₁ i) U
 have he: distribute Y H (0+v) (I₁ i) F = distribute Y H (0+v) (I₁ i) (F₀ i):=by
    change distribute Y H (0+(0+r+1)) _ _=_
    rw [nativeBox Y H 0 v S _ _ U e₀ t₀ v₀]; unfold U; rw [Lariat.parcel,respan]
    have hw: Satin.PairIdx Y (0+(0+r)) (I₁ i) (K₁ i):=⟨t₀.1, t₀.2⟩
    rw [show respan Y H 0 (I₁ i) (K₁ i) (padTop _ _)=1 from respan_holds Y H (I₁ i) (K₁ i) 0 r ⟨t₀.1, ?_⟩,ascendUnit Y _ _ _ hw,one_mul]; rfl
    have he:=hw.2; unfold r at *; omega
 change sharp Y H (0+v) _ _ F =Φ i
 rw [show sharp Y H (0+v) _ _ F=sharp Y H (0+v) _ _ (F₀ i) from congrArg (Journey.compass Y (I₁ i) (K₁ i) (0+v)) he]
 change sharp Y H (0+(0+r+1)) _ _ _ = _; rw [hz]
lemma quoteSelected (s:ℕ)(f:Lariat K n): Tendsto (fun i=> let m:= n+((A i).t-(s+n+1))+1; sharp Y H (s+m) (I₁ i) (K₁ i) (priceAt Y H s (I₁ i) (K₁ i) (Lariat.parcel Y H d (A i) s f)) / sharp Y H (A i).t (I₁ i) (K₁ i) (Future.kernelPath Y H d (A i)).val) atTop (𝓝 (appeal Y H D G d c (M.character y) T s f)):=by
 have he:= (p.move n s f).div (pieceSame Y H D G u t d c M y A w p) one_ne_zero; rw [div_one] at he; exact he
end weights

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
