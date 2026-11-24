import YM.SU5.FiniteGaugeData.Mist.Ore
import YM.SU5.FiniteGaugeData.KernelP.Price
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Mist
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
variable (B:List Axis)
local notation "M"=> H.space
section
variable (K:Calibration)(B:List Axis)(t t':Four ℤ)(x:W K)
def hourS (x:W K) : List Axis→ W K
 | []=>x
 | b::v=>clockW K b (t b) (hourS x v)
#print hourS.eq_2
abbrev orbitW (t:Four ℤ)(x:W K): W K:= hourS K t x Terrace.scheduleL
lemma hourS_com b z : clockW K b z (hourS K t x B)=hourS K t (clockW K b z x) B:= by induction B with
 | nil=>rfl
 | cons i v ih=> rw [hourS.eq_2,hourS.eq_2,clock_cross,ih] -- at clock b ...
lemma hourS_add: hourS K t (hourS K t' x B) B= hourS K (t+t') x B:=by induction B with
 | nil => rfl
 | cons i v ih=> rw [hourS.eq_2,hourS.eq_2,hourS.eq_2,←hourS_com, ih,clock_add]; rfl
lemma orbitW_o : orbitW K 0 x=x:=by simp [orbitW,Terrace.scheduleL,hourS]
lemma hourS_single (z:ℤ): orbitW K (Pi.single a z) x=clockW K a z x:=by fin_cases a<;> simp [orbitW,Terrace.scheduleL,hourS]
lemma orbitW_add : orbitW K t (orbitW K t' x)=orbitW K (t+t') x:=hourS_add K Terrace.scheduleL t t' x
lemma hourS_prod (y:W K): hourS K t (x*y) B= (hourS K t x B)*(hourS K t y B):=by induction B with
 | nil=>rfl
 | cons z q ih=> rw [hourS.eq_2, ih,clock_mul]; rfl
lemma hourS_id : hourS K t 1 B=1:=by induction B with
 | nil=>rfl
 | cons z q ih=> rw [hourS.eq_2,ih,clock_one]
lemma sailing (v:List (W K)): orbitW K t v.prod=(v.map (orbitW K t)).prod:=by induction v with
 | nil=> exact hourS_id K Terrace.scheduleL t -- order? 
 | cons i v ih=>
    have he:=hourS_prod K Terrace.scheduleL t i v.prod; change orbitW K t (i*v.prod)=_; exact he.trans (congrArg (fun z=> orbitW K t i * z) ih)
end
local notation "V"=> Carousel Λ.R.L
local notation "S₀"=> Terrace.scheduleL
variable (t:Four ℤ)
include S' in
lemma cross_paid (x:W (tent Y h)): Φ s (orbitW Kₜ t x) = Φ s x:= payH_ Terrace.scheduleL
where payH_ (B:List Axis): Φ s (hourS Kₜ t x B) = Φ s x:= by induction B with
       | nil=>rfl
       | cons i v ih=> rw [hourS.eq_2, S'.color,ih]

-- identification of any taped sequence
variable (X:Engine Y h W' R a H)
-- B axis ignored time part of Maneu. use erased time in actual markup.
local notation "t'"=>Function.update t a (0:ℤ)
include X
lemma warmth : ∃ y:Decko Y h a, Maneu X.val (reportQ s t) B (H.leaf s x)= H.leaf s y ∧ y.val= hourS Kₜ (Function.update t a 0) x.val B:= by
 induction B with
 | nil=> exact ⟨x,rfl,rfl⟩
 | cons i v ih=>
    obtain ⟨y,p,q⟩:=ih
    let U:= Maneu X.val (reportQ s t) v; change ∃ z:Decko Y h a,ramble X.val i (ticQ L₁ s (t i)) (U (H.leaf s x))= H.leaf s z∧z.val=clockW Kₜ i ((t') i) _; rw [show U (H.leaf s x)= _ from p]
    by_cases e:i=a; · subst i; exact ⟨y,(DFunLike.congr_fun (ramble_self ..) _),q.trans (by simp)⟩ -- q turns simp direction
    rw [ramble_eq _ _ _ e,Driver_eq]; refine ⟨_,X.property ..,?_⟩; rw [hoist_val,q,Function.update_of_ne e]
open scoped NNReal ENNReal
local notation "Q"=> (Carousel Λ.R.L)
-- relative Duet.S.We compute heat duration on a-view REAL.
end Mist
end YM.CF.Buffered.Afterglow.Hierarchy
