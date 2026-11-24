import ZecaBern
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin Vp.Folio
variable {H:Hilbert}{ι:Type}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(Ω:H.space)
 (hΩ:∀x:E4,M S x Ω=Ω)
local notation "a"=>timeAxis
local notation "Λ"=>List (Item G.Chip)
local notation "φ"=>face S Ω G.dep G.grade
local notation "ψ"=>role S Ω G.dep G.grade

variable (b:Axis)(h:b≠timeAxis)(r:ℝ)
abbrev xp: E4→ₗ[ℝ]ℝ:= (PiLp.proj (p:=2) (𝕜:=ℝ) (β:=fun _ : Axis=>ℝ) b).toLinearMap
include h in lemma xp_zero: xp b (basis timeAxis)=0:=by change basis a b=0; simp [Ne.symm h,h]
abbrev bank (h:b≠timeAxis):Cross timeAxis:=⟨basis b,by change basis b a=0; simp [Ne.symm h,h]⟩
abbrev Sunny: Set H.space:= {y|∃ L:List (Item G.Chip), LaneE timeAxis 0 L ∧ LaneE b r L ∧ y=φ 0 L}
abbrev Sunset: Set H.space:= {y|∃ L:List (Item G.Chip), BackE timeAxis 0 L ∧ BackE b r L ∧ y=ψ 0 L}
lemma rise₀: FarJ S G Ω (xp b) r ⊆ Sunny S G Ω b r:=by
 have n: xp b≠0:=by
    intro p
    have z: xp b (basis b)=1:=by change basis b b=1;simp
    rw [p,LinearMap.zero_apply] at z;norm_num at z
 rintro _ ⟨L,t,q,f,h⟩
 exact ⟨L,t,⟨q.imp fun a'=>(a'.resolve_left n),fun y v=> (h y v).resolve_left n⟩,f⟩

include h
lemma west : FarJ S G Ω (-xp b) (-r)⊆Sunset S G Ω b r:=by
 have n: -xp b≠0:=by
    intro p
    have z: (-xp b) (basis b)= -1:=congrArg Neg.neg (show basis b b=1 from by simp)
    rw [p, LinearMap.zero_apply] at z;norm_num at z
 rintro x ⟨L,t,q,f,u⟩
 let B:= G.mirrorK
 let v:= mirrorsK timeAxis B
 have e(i:Item G.Chip):timesA b (v i)=timesA b i:=by change orbitT a i.2 b=i.2 b; simp [orbitT,h]
 have g:=fore_a 0 L B t
 have d:=ok_back S Ω G.dep G.grade 0 L B (fun _=>rfl) (fun i=>(G.spar i).symm) t
 rw [neg_zero] at g d
 refine ⟨_,g,⟨List.pairwise_reverse.mpr (List.pairwise_map.mpr (q.imp ?_)),?_⟩,f.trans d.symm⟩
 · intro i j p; change timesA b (v j)<timesA b (v i)
   rw [e,e];exact neg_lt_neg_iff.mp (p.resolve_left n)
 intro i p;obtain ⟨i,f,rfl⟩:= List.mem_map.mp (List.mem_reverse.mp p)
 rw [e]; exact neg_lt_neg_iff.mp ((u i f).resolve_left n)
lemma bany : ‖bank b h‖≤1:=by
 change ‖basis b‖ ≤ 1
 exact le_of_eq (by simp [basis])

variable (HF:Celeritas.Cinema S) (p:Filled S G Ω)
include hΩ HF p
lemma southRise:Annihilated S (Sunny S G Ω b r):=by
 have d:0<xp b (bank b h).val:=by change 0<basis b b;simp
 exact fun x hx=>tickets S G Ω hΩ (xp b) (xp_zero b h) HF (bank b h) (bany b h) d r p x
       (fun y u=>hx y (rise₀ S G Ω b r u))
lemma southWest:Annihilated S (Sunset S G Ω b r):=by
 have d:0<(-xp b) (-bank b h).val:=by change 0 < -(-(basis b b));simp
 exact fun x hx=>tickets S G Ω hΩ (-xp b)
    (show -xp b (basis timeAxis)=0 by rw [xp_zero b h,neg_zero]) HF (-bank b h)
    (by rw [norm_neg];exact bany b h) d (-r) p x (fun y u=>hx y (west S G Ω b h r u))
#print axioms southWest
#print axioms southRise