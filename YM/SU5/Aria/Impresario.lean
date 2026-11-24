import YM.SU5.Aria.Vesper
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "b₀"=>ruler P.par.block
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "X"=> P.ColorHil j x
local notation "Y"=> P.ManyF j x
local notation "Θ" i:max=> P.reflectTest i
local notation "Γ"=> P.VMark
variable (k:Trans j) (D:P.Apron)(n t:ℕ)
local notation "λ₀"=> P.blade j x k
local notation "π"=> P.fansM j x k
local notation "κ"=> P.enter j x
local notation "ρ"=> P.wealth j x
-- convivial doors
local notation "μ" F:max=> (P.birthF j n F)
local notation "ν" F:max=> (P.viewF j x n F)
local notation "f̂" y:max=>P.voxTest j n y
namespace Apron
local notation "d"=>D.zoom P n j
local notation "P₀"=>D.engine P j x
local notation "Ψ"=>P.shifts j d (D.full P n)
lemma overnight (p:D.s≤n){F:P.Test}(g:μ F): ∃ h:P.birthF j n (P.shifts j (zoom P D n j) (full P D n)* P.shifts j ((d:ℕ)+d) F), P.viewF j x n h=P₀ (P.viewF j x n g):=by
 obtain ⟨u,t,e⟩:= D.full_realizes P j n p; have ht:P.voxTest j n u.val∈enclave K:=t ▸ P.shifts_keep j _ (D.fullColor P n); let w:=d+d; have hw:0<w:=add_pos (D.zoomP P j n) (D.zoomP P j n); obtain ⟨a,q⟩:=P.accepted_view j x n w hw u ht g
 have he:P₀=Φ (P.door j n w hw u ht):= congrArg (fun u:P.Physical j=> Φ u) (Subtype.ext (a1:=P.door j D.s _ (add_pos (D.pos j) (D.pos j)) (D.cardB P j) (D.color P j)) (a2:=P.door j n w hw u ht) e)
 have hs:f̂ u.val* P.shifts j (w:ℤ) F=P.shifts j d (D.full P n)*P.shifts j ((d:ℕ)+d) F:=by rw [t]; unfold w; norm_cast -- !! term `(d:ℕ)+d` elaborates ℤ?? type checked
 have hu: μ (P.shifts j d (D.full P n)*P.shifts j ((d:ℕ)+d) F):=by rw [←hs]; exact a
 refine ⟨hu,(P.identical_F j x n hu a hs.symm).trans ?_⟩; exact q.symm.trans (congrArg (fun z:(P.ColorHil j x).Op=>z (ν g)) he.symm)
variable {D}
lemma full_exchange (D:P.Apron) (k:Axis): full P (D.kiss P k) n = (Θ k) (D.full P n):= (P.reflUp D.s n k D.F) -- name
variable (D)
local notation "D₁"=>D.kiss P k.val
lemma entourage (v: D.s ≤ n){x':P.Test}(p:μ x') : λ₀ (P₀ (P.viewF j x n p))=(D₁).engine P j x (λ₀ (P.viewF j x n p)):=by
 let X':=ν p; obtain ⟨t,T⟩:= D.overnight P j x n v p; let g:= P.crew_flies j k n p; obtain ⟨y,u⟩:=(D₁).overnight P j x n v g; rw [←T,P.blade_view,P.blade_view,← u]; apply P.identical_F j x n _ _; -- parse
 have h:(D₁).zoom P n j=D.zoom P n j:= rfl; rw [h,full_exchange]
 have he(x y:P.Test): (Θ k.val) (x*y)=(Θ k.val) x*(Θ k.val) y:=aureoleProduct ..; rw [he]; exact congrArg₂ (·*·) (P.meetrefl j k.val _ _ (Ne.symm k.property)).symm (P.meetrefl j k.val _ _ (Ne.symm k.property)).symm
lemma antiMeasure(y:X): λ₀ (P₀ y)=(D₁).engine P j x (λ₀ y):=by
 apply congrArg (fun f:Muse (P.ColorHil j x)=>f y) (show (λ₀).comp P₀=((D₁).engine P j x).comp (λ₀) from ?_)
 apply starinter _ (P.partner_dense j x); intro i
 rcases i with ⟨t,f,p⟩; let F:=P.viewF j x t p; let a:=max t D.s; have ht:t≤ a:=le_max_left ..; change λ₀ (P₀ F)=(D₁).engine P j x (λ₀ F); unfold F; rw [← P.view_rig j x t a p ht]; exact D.entourage P j x k a (le_max_right ..) _
lemma swirl (p:Vantage) (u:Y): π (P.tableau j x p P₀ u)= P.tableau j x (mirrorΩ k.val p) ((D₁).engine P j x) (π u):=by
 let W:= (D₁).engine P j x; let V:= P.cartage j x; let T:=mirrorΩ k.val p
 change π (V p (ρ (P₀ (κ (V (-p) u)))))= V T (ρ (W (κ (V (-T) (π u)))))
 unfold V; rw [P.fan_march,← P.bank_companion j x k, D.antiMeasure P j x k,← P.entersM,P.fan_march,mirrorΩ_neg]
-- time turns about axis j instead. engine's slab op is exactly adjoint
local notation "D₂"=> D.kiss P j
local notation "L₀"=>D.s
local notation "c"=>D.u j
local notation "G₀"=> D.cardB P j
local notation "B"=> ((D₂).cardB P j)
lemma shiftHat : mirror K j (gaugeT K (((c+c:ℕ):ℤ))) (relocate K j (c:ℤ) D.F.val) = relocate K j (c:ℤ) (mirror K j 0 D.F.val):=by
 let z:ℤ:=c; let f:Dome K:=D.F; have he:=SlabMark.odd_cancel K j (((c+c:ℕ):ℤ)) 0 z ((marque K).mp D.F.property); rw [gaugeT_zero] at he -- notation κ enter issue
 have hw:(((c+c:ℕ):ℤ))-0-z=z:=by unfold z; omega
 rw [hw] at he; exact he
lemma kiss_entry : SlabMark.inverse P.run P.large D.s j false (c+c) G₀= (show P.Card j D.s (c+c) from B):= Subtype.ext (Subtype.ext (shiftHat P j D))
local notation "π₀" D:max=>P.door j D.s _ (add_pos (D.pos j) (D.pos j)) ((D).cardB P j) ((D).color P j)
private lemma stashed : star (π₀ D)=(π₀ (D₂)):= by
 apply Subtype.ext
 change star (P.atSide _ _ _ _ G₀) = P.atSide j D.s (c+c) _ B
 rw [P.grainStar,kiss_entry]; -- proof irrelevance
private lemma star_troupe (A:Type*) [CStarAlgebra A](V:Hilbert)(F:A →⋆ₐ[ℂ] V.Op)(x y:A)(p:star x=y):star (F x)=F y:=by rw [← map_star F,p]
lemma peer : star (D.engine P j x)=(D₂).engine P j x:=by
 exact star_troupe (P.Physical j) (P.ColorHil j x) (Φ) (π₀ D) (π₀ (D₂)) (D.stashed P j)
end Apron
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Apron.peer
