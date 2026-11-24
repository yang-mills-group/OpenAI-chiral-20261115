import Velour.Crepe.Aperture

/-!
# Gallery. All the pieces, honestly arrived at fixed positive
thickness. Dense with even one sleeve at a time, NOT just dense span.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 800000
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

local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E
local notation "m"=> timeMesh P.par
local notation "Q" => P.shifts j
local notation "L"=> P.par.R.L.val
variable {s t v w:ℕ}
-- Domes have compact footprint. Thus attainable width in all axes at once;
-- pay even at the stated reading resolution.
private lemma verge (S:Finset Cover)(a:Axis): ∃d:ℕ,0<d ∧ Between K a (-(ruler (K).B)*d) (ruler (K).B*d) S := by
 let f (x:Cover):= Int.natAbs (x a)
 obtain ⟨n,q⟩ := Finset.exists_nat_subset_range (S.image f)
 let b:=ruler (K).B
 have hb:1≤b := Int.add_one_le_of_lt (b:=(b)) (ruler_gene _)
 refine ⟨n+(K).ℓ+1,by omega,fun z hz=>?_⟩
 have hn:Int.natAbs (z a)<n:=Finset.mem_range.mp (q (Finset.mem_image_of_mem _ hz))
 have e:(n+(K).ℓ+1:ℕ)≤b*(n+(K).ℓ+1:ℕ) := le_mul_of_one_le_left (by positivity) hb
 rw [neg_mul]
 unfold b at e
 omega

private lemma verges (S:Finset Cover){u:ℕ} (q:0<u)
 (r: Between K j (-ruler (K).B*u) (ruler (K).B*u) S) :
 ∃d:Axis→ℕ, d j=u ∧ (∀a,0<d a) ∧
 (∀a, Between K a (-ruler (K).B * d a) (ruler (K).B * d a) S):=by
 choose e p t using verge P S
 
 refine ⟨fun a=> if a=j then u else e a, if_pos rfl, ?_,?_⟩
 · intro a; by_cases h:a=j <;> simp only [h,↓reduceIte]; exact q; exact p a
 · intro a; by_cases h:a=j <;> simp only [h,↓reduceIte]; exact r; exact t a


lemma all_aprons (s:ℕ)(y:P.Test)(q:y∈enclave K): ∃A:P.Apron,A.s=s ∧ A.F=y := by
 obtain ⟨⟨S,p⟩,_⟩ := y.property
 choose d h w using verge P S
 exact ⟨⟨s,d,h,y,S,p,q,w⟩,rfl,rfl⟩

-- frame even card
variable {P j x}
lemma ThreadOp.frame {y:P.Test}{T:(P.ColorHil j x).Op}
 (h:P.ThreadOp j x s (v+v) y T):
 ∃A:P.Apron,A.engine P j x=T := by
 have e:=h.pos
 obtain ⟨c,_,p,t,_⟩:= (show P.ThreadOp _ _ _ _ _ _ from h)
 have p':y∈enclave K:= t.symm ▸ p
 obtain ⟨S,a,b⟩:= c.property
 have a':Q (-v:ℤ) y∈ bay K (plow K j (-v:ℤ) S) true:= P.shifts_support _ _ _ (show y∈bay K S true from t.symm ▸ (show P.voxTest j s c.val ∈ bay K S true from a))
 have g:=Between.relocate K j b (-v:ℤ)
 rw [show ruler (K).B*(-v:ℤ)+0= -ruler (K).B*v by ring,
     show ruler (K).B*(-v:ℤ)+ruler (Λ).block*↑(v+v)=ruler (K).B*v by change _+ruler (K).B*↑(v+v)=_; push_cast; ring] at g
 obtain ⟨d,r,u,m'⟩ := verges P j _ (by omega : 0<v) g
 let A:P.Apron:=⟨s,d,u,Q (-v:ℤ) y,_,a',P.shifts_keep _ _ p',m'⟩
 have q:=A.sewn (x:=x)
 have w:A.u j=v:=r
 rw [w,show A.F=Q (-v:ℤ) y from rfl,P.shifts_sum,add_neg_cancel,P.shifts_zero] at q
 exact ⟨A, q.unique h⟩



variable (P j x)
def OnShow(y:X) := ∃s w f T,P.ThreadOp j x s w f T ∧ T ω=y
abbrev launched (s:ℕ)(y:X):= ∃w f T,P.ThreadOp j x s w f T ∧ T ω=y
variable {P j x}{b d:P.ColorHil j x}
lemma OnShow.fine (p:P.OnShow j x b): ∀ᶠ s in atTop,P.launched j x s b:=by
 obtain ⟨t,w,y,T,h,r⟩:=p
 filter_upwards [eventually_ge_atTop t] with s hs
 exact ⟨_,_,_,h.higher hs,r⟩
lemma ThreadOp.hangs {f:P.Test}{T:(P.ColorHil j x).Op}
 (p:P.ThreadOp j x s w f T) (k:ℕ):
 ∃U, P.ThreadOp j x s (w+k) f U ∧ U ω=T ω:=
 ⟨_, p.aft k, by rw [mul_apply_eq_comp,P.sector_hot]⟩

lemma OnShow.plus (p:P.OnShow j x b) (q:P.OnShow j x d):P.OnShow j x (b+d):=by
 obtain ⟨t,⟨u,f,T,h,rfl⟩,v,g,U,k,rfl⟩ := (p.fine.and q.fine).exists
 obtain ⟨S,l,a⟩ := h.hangs v; obtain ⟨Z,r,z⟩:=k.hangs u
 rw [add_comm] at r
 exact ⟨_,_,_,_,l.add r, (add_apply S Z _).trans (congrArg₂ (·+·) a z)⟩


lemma OnShow.times (p:P.OnShow j x b) (c:ℂ):P.OnShow j x (c • b):=by
 obtain ⟨t,w,y,T,h,rfl⟩:=p
 exact ⟨_,_,_,_,h.smul c,rfl⟩

lemma OnShow.frames (p:P.OnShow j x b): ∃A:P.Apron, A.engine P j x ω=b:=by
 obtain ⟨t,w,y,T,h,r⟩:=p
 obtain ⟨U,f,e⟩:=h.hangs w
 obtain ⟨A,u⟩:=f.frame
 exact ⟨A,u ▸ (e.trans r)⟩
lemma literal_framed (p:b∈ P.colorSpan j x): ∃A:P.Apron,A.engine P j x ω=b:=by
 refine OnShow.frames ?_
 induction p using Submodule.span_induction with
 | zero=> exact ⟨0,1,0,0,ThreadOp.zero one_pos,rfl⟩
 | add _ _ _ _ i j=> exact i.plus j
 | smul _ _ _ i=> exact i.times _
 | mem u h=>
   obtain ⟨s,f,rfl⟩:=show ∃s,∃f,_ from mem_iUnion.mp h
   obtain ⟨w,p,k,q⟩:=P.fits j s f.val
   have hk:P.voxTest j s k.val∈enclave K:=by rw [q]; exact f.property
   refine ⟨s,w,_,_,⟨k,p,hk,rfl,rfl⟩, (P.awake j x s w p k hk).trans (congrArg _ (Subtype.ext q))⟩

variable (P j x)
theorem single_canvas_dense : DenseRange (fun A:P.Apron=>A.engine P j x ω):=
 (P.native_dense j x).mono (fun _ y=>literal_framed y)

theorem single_sleeve_dense : DenseRange
    (fun A:P.Apron=>P.wealth j x (A.engine P j x ω)):=by
 have h:Surjective (P.wealth j x):= fun y=>⟨_,P.rewarded j x y⟩
 exact h.denseRange.comp (P.single_canvas_dense j x) (P.wealth j x).continuous
#print axioms single_sleeve_dense
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
