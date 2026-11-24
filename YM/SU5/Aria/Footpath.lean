import YM.SU5.Aria.Crew
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
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "u"=> enclave P.calibration
local notation "X"=> P.ColorHil j x
variable (n:ℕ)
local notation "π" w:max p:max f:max e:max=> P.door j n w p f e
local notation "ϕ" v:max=>P.voxTest j n v
local notation "μ"=>P.birthF j n
local notation "ν"=>P.viewF j x n
local notation "S"=>P.shifts j
lemma admitted_view {w:ℕ}(f:P.Card j n w)(e:ϕ f.val∈ u): P.birthF j n (ϕ f.val) :=⟨⟨f.val,e⟩,rfl⟩
lemma attended {w:ℕ}(p:0<w)(f:P.Card j n w)(e:ϕ f.val∈ u): Φ (π w p f e) ω=ν (P.admitted_view j n f e):= by rw [P.awake]; exact (P.holdsF j x n _ (⟨f.val,e⟩:P.naturalVox j n) rfl).symm
private lemma handy_doors (A:Type*) [CStarAlgebra A](B:Hilbert) (σ:A →⋆ₐ[ℂ] B.Op)(a b c:A)(x:B)(h:a*b=c):σ a (σ b x)=σ c x:=by subst c; rw [map_mul]; rfl
private lemma accepted_cast (w:ℕ)(p:0<w)(f:P.Card j n w)(e:ϕ f.val∈ u)(v:ℕ)(pv:0<v)(k:P.Card j n v)(h: (ϕ k.val)∈u)(x':P.birthF j n (ϕ k.val)): ∃ uv: μ ((ϕ f.val)* S (w:ℤ) (ϕ k.val)), Φ (π w p f e) (ν x')=ν uv:=by
 let F:=edit Y₀ H n j false w v f k; have he: (ϕ f.val)* (S (w:ℤ) (ϕ k.val))=ϕ F.val:=Subtype.ext (editor ..).symm
 have ht: ϕ F.val∈u:= he ▸ Subalgebra.mul_mem u e (P.shifts_keep j w h)
 have hv: μ ((ϕ f.val)* (S (w:ℤ) (ϕ k.val))):=he ▸ P.admitted_view j n F ht
 refine ⟨hv,?_⟩; have h₁:ν hv=ν (P.admitted_view j n F ht):= P.identical_F j x n hv (P.admitted_view j n F ht) he -- syntax
 have hcat: π w p f e* (π v pv k h)=π (w+v) (add_pos p pv) F ht:=Subtype.ext (P.concat ..)
 -- use defeq
 have hh:=handy_doors (P.Physical j) (P.ColorHil j x) (Φ) _ _ _ ω hcat
 exact (congrArg (fun y: P.ColorHil j x=> Φ (π w p f e) y) (P.attended j x n pv k h).symm).trans (hh.trans ((P.attended j x n (add_pos p pv) F ht).trans h₁.symm))
set_option maxHeartbeats 1000000 in
lemma accepted_view (w:ℕ)(p:0<w)(f:P.Card j n w)(e:ϕ f.val∈ u){g:P.Test}(h:μ g): ∃ uv: μ ((ϕ f.val)* S (w:ℤ) g), Φ (π w p f e) (ν h)=ν uv:=by
 let k:=P.emmigrant j n h; obtain ⟨v,pv,f',t⟩:= P.fits j n k.val
 have he:ϕ f'.val=g:=(congrArg (P.voxTest j n) t).trans (P.documented j n h); have hp:ϕ f'.val∈u:= t ▸ k.property
 obtain ⟨s,pB⟩:=accepted_cast P j x n w p f e v pv f' hp (P.admitted_view j n f' hp)
 have hv: μ ((ϕ f.val)* S (w:ℤ) g):=by rw [←he]; exact s
 refine ⟨hv,(congrArg (fun a:X => Φ (π w p f e) a) (P.identical_F j x n h (P.admitted_view j n f' hp) he.symm)).trans ?_⟩
 exact pB.trans (P.identical_F j x n s hv (by rw [he]))
lemma view_one : P.viewF j x n (P.faceUnit j n) = P.colorZero j x:=by
 let p:=Nat.zero_le n
 have he: P.conveying 0 (n-0) 1=1:=Subtype.ext (woven_one Y₀ H P.history.circuit ..)
 rw [P.identical_F j x n (P.faceUnit j n) (P.rig j 0 n (P.faceUnit j 0) p) he.symm, P.view_rig j x 0 n (P.faceUnit j 0) (Nat.zero_le _),P.holdsF j x 0 (P.faceUnit j 0) (⟨unity Y₀ H j 0 false 0,P.firstVox j 0⟩ : P.naturalVox j 0) rfl]; exact P.identified0 ..
lemma view_scalar {g:P.Test}(h:μ g): inner ℂ ω (ν h)= P.singleState j n x g:=by rw [← P.view_one j x n,P.released_gram,show P.reflectTest j 1=1 from aureoleUnit ..,one_mul]
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "E"=> (P.physicalEnergy j x).E

section assemble
variable {I:Type*} (A:I→P.Apron)(r:I → Cover)
abbrev firstLeg (i:I) :ℤ := r i j - (A i).zoom P n j
abbrev lastLeg (i:I) :ℤ := r i j + (A i).zoom P n j
local notation "a✩"=>P.firstLeg j n A r
local notation "b✩"=>P.lastLeg j n A r
def onBoard : List I→ ℤ→Prop
 | [],_=> True
 | i::L,b=> b ≤ a✩ i ∧ onBoard L (b✩ i)
abbrev boxL (i:I) : (X).Op:= P.charter j x (P.vtile n (r i)) ((A i).engine P j x)
def eRide : List I→ℤ→ X
 | [],_ => P.colorZero j x
 | i::L,b => E (whenly (timeMesh P.par) n ((firstLeg P j n A r i-b).toNat)) (boxL P j x n A r i (eRide L (lastLeg P j n A r i)))
def fullScroll (L:List I) : P.Test:= (L.map (fun i=>P.chartAll (r i) ((A i).full P n))).prod
local notation "D" => P.fullScroll n A r
local notation "W"=> P.eRide j x n A r
lemma vread (L:List I)(b:ℤ)(t:P.onBoard j n A r L b)(h:∀ i∈ L,(A i).s≤n):
    ∃ hv:P.birthF j n (S (-b) (P.fullScroll n A r L)), P.viewF j x n hv=P.eRide j x n A r L b:=by
 induction L generalizing b with
 | nil=>
   have he: S (-b) (D [])=1:=map_one (S (-b)); exact ⟨he ▸ P.faceUnit j n,(P.identical_F j x n _ (P.faceUnit j n) he).trans (P.view_one j x n)⟩
 | cons i L ih=>
   let a:= a✩ i; let p:= A i; let c:= b✩ i; let d:= (a-b).toNat; let v:=p.zoom P n j; let z:= P.chartAll (r i) (p.full P n)
   obtain ⟨α,q⟩:= t; have hd:(d:ℤ)=a-b:= Int.toNat_of_nonneg (sub_nonneg.mpr α)
   obtain ⟨f,tF,B,g⟩:= p.transported P j x n (h i (List.Mem.head ..)) (r i); have e:0<v+v:=add_pos (p.zoomP P j n) (p.zoomP P j n)
   obtain ⟨β,xz⟩:=ih c q (fun i u' => h i (List.Mem.tail _ u'))
   obtain ⟨Z,Y⟩:= P.accepted_view j x n _ e f tF β
   let V:=P.passesLater j n d Z; have hu:S (-b) (D (i::L))=S (d:ℤ) ((ϕ f.val)*S ((v+v:ℕ):ℤ) (S (-c) (D L))):= by
      change S (-b) (z*D L)=_; change ϕ f.val=S _ z at B; rw [B,map_mul,map_mul,P.shifts_sum,P.shifts_sum,P.shifts_sum]
      apply congrArg₂ (·*·) <;> apply congrArg (fun a=>S a _) <;> try change (-(b:ℤ))=_
      · rw [hd]; unfold a firstLeg p; omega
      rw [hd]; unfold c a firstLeg lastLeg v p; omega
   have hi: μ (S (-b) (D (i::L))):=by rw [hu]; exact V
   refine ⟨hi,(P.identical_F j x n hi V hu).trans ?_⟩; change ν (P.passesLater j n d Z)= E (whenly Μ n d) (P.charter j x (P.vtile n (r i)) (p.engine P j x) (W L c)); refine (P.releasedLater j x n d Z).trans (congrArg (fun y:(P.ColorHil j x).space=> E (whenly Μ n d) y) ?_)
   exact Y.symm.trans (congrArg₂ (fun (U:(P.ColorHil j x).Op) (v:(P.ColorHil j x).space)=>U v) g.symm xz)
lemma fullScroll_perm {L L':List I}(t:L.Perm L'): P.fullScroll n A r L=P.fullScroll n A r L':=t.map _ |>.prod_eq
lemma full_scroll_effect (L:List I) : D L∈ enclave (K):=by
 induction L with
 | nil=>exact Subalgebra.one_mem _
 | cons i L h=>exact (enclave K).mul_mem (P.cruise_color Vacancy.ordinate (r i) ((A i).fullColor P n)) h
lemma wagon (L:List I)(b:ℤ)(t:P.onBoard j n A r L b)(h:∀ i∈ L,(A i).s≤ n):
    inner ℂ ω (P.eRide j x n A r L b) = P.singleState j n x (D L):=by
 obtain ⟨v,hv⟩:= P.vread j x n A r L b t h; rw [← hv,P.view_scalar,P.slide_single]
end assemble
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.wagon
