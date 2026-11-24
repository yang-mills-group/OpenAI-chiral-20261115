import Velour.Gathers.Rhythm
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Velour Boundary Probe
local notation "R"=> S.gauze
local notation "B"=> S.weight
local notation "D"=> S.muslin
local notation "U"=> S.unit.translation

def CordPair (z:H)(f:Test4)(X Y:H.Op):ℂ:=
 ∫y:E4, f y * inner ℂ (X z) (U y (Y z))

variable {v:S.muslin} (h: ∀y:E4,S.unit.translation y v.val=v.val)
include h

lemma pairedCord (X Y:H.Op)(f:Test4):
   S.CordPair v.val f X Y= inner ℂ (X v.val)
                     (S.labelled Y f v).val:=by
 rw [labelled_coe, rasp_apply,← integral_inner (S.unsoiled Y f v.val)]
 refine integral_congr_ae (ae_of_all _ fun b=>?_ )
 simp only [inner_smul_right, dangle,mul_apply_eq_comp,h]


lemma weighedCord (m:ℕ)(X Y:H.Op)(f:Test4):
  S.CordPair v.val f X Y=
    inner ℂ (S.wrapW m X (B m v).val) (B m (S.labelled Y f v)).val:=by
 rw [S.pairedCord h,wrapW,mul_apply_eq_comp,weight_cancel,mul_apply_eq_comp]
 have z:=congrArg (· ^ m) S.gauze_star
 have e:star (R^m)=R^m:=by rw [star_pow,S.gauze_star]
 have p(y z:H) : inner ℂ ((R^m) y) z= inner ℂ y ((R^m) z):=
    by nth_rw 1 [←e]; exact ContinuousLinearMap.adjoint_inner_left ..
 rw [p,S.weight_cancel]


variable {ι:Type}{F:ι→Test4}{f:Test4}{l:Filter ι}{A C:ι→H.Op}
lemma tendstoCord {m:ℕ}{X:H.Op}{T:S.Detector}
   (p:∀ z:H, Tendsto (fun i=>S.wrapW m (A i) z) l (𝓝 (X z)))
   (t:S.Surges l (fun i=>S.labelled (C i) (F i)) (T f)):
   Tendsto (fun i=>S.CordPair v.val (F i) (A i) (C i)) l
      (𝓝 (inner ℂ (X (B m v).val) (B m ((T f) v)).val)):= by
 refine ((p _).inner (𝕜:=ℂ) (t.at_one v m)).congr ?_
 exact fun i=> (S.weighedCord h m (A i) (C i) (F i)).symm



variable {S}
local notation "E"=> S.E
omit h

lemma Prepaid.gaze {m:ℕ}{Q:ℝ≥0→H.Op}{X:H.Op}
   (q:S.Prepaid Q m X)(z:H):
  Tendsto (fun d=> S.wrapW m (Q d) z) (𝓝[>] (0:ℝ≥0)) (𝓝 (X z)):=by
 have g:Tendsto (fun d=>E d (X (E d z))) (𝓝 (0:ℝ≥0)) (𝓝 (X z)):=by
   have p:= continuous_id.prodMk (X.continuous.comp (S.continuousE z))
   have k:Continuous fun d=>E d (X (E d z)):= S.heat_breed.comp p
   have t:= k.tendsto 0
   rw [show X z= E 0 (X (E 0 z)) by rw [S.eZero]; rfl]
   exact t
 exact (g.mono_left nhdsWithin_le_nhds).congr' (eventually_mem_nhdsWithin.mono
    fun d p=>(congrArg (fun A:H.Op=>A z) (q d p)).symm)


lemma Ribs.gaze_warm {m:ℕ}{Q:ℝ≥0→H.Op}{X:H.Op}{Y:ℕ→H.Op}{t:ℝ}{j:ℕ→ℕ}
  (q:S.Ribs Y Q m t X)
  {a b:ℕ→ℝ≥0}(p:Tendsto j atTop atTop)
  (e:Tendsto a atTop (𝓝 0))(g:Tendsto b atTop (𝓝 0)):
    Gleams H (fun i=> S.wrapW m (E (a i)*Y (j i)* E (b i))) X:=by
 let n:= ((Gleams.warm S e).mul (q.rattle.glints p)).mul (Gleams.warm S g)
 rw [show E 0=1 from S.eZero,one_mul,mul_one] at n
 refine n.agree (Eventually.of_forall ?_)
 intro i
 dsimp only [Function.comp_apply,wrapW]
 have ua:=((S.gauze_heated (a i)).pow_right m).eq
 have ub:=((S.gauze_heated (b i)).pow_right m).eq
 rw [←mul_assoc,←mul_assoc (E (a i)),ua, mul_assoc (_*_*_),(Eq.symm ub)]
 simp only [mul_assoc]
#print axioms tendstoCord

