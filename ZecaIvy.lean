import ZecaSeed
import YM.SU5.FiniteGaugeData.Poin.Loot
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


variable {H:Hilbert} (X:Set H.space)

open Submodule
abbrev Boxed := (Submodule.span ℂ X).topologicalClosure
instance:CompleteSpace (Boxed X):=isClosed_closure.completeSpace_coe

lemma grown (y:H.space)(p:y∈X): y∈ Boxed X:= Submodule.le_topologicalClosure _ (Submodule.subset_span p)
lemma manyKeeps {A:H.Op}(h:∀y∈X,A y∈Boxed X): Keeps (Boxed X) A:=
 let a := Submodule.span ℂ X
 let ha: a≤ (Boxed X).comap A.toLinearMap:= Submodule.span_le.mpr h
 fun x p=> a.topologicalClosure_minimal ha (show IsClosed _ from
    (show IsClosed ((Boxed X):Set H.space) from isClosed_closure).preimage A.continuous) p

local notation "J"=>Boxed X
local notation "Q"=> Submodule.starProjection (Boxed X)
lemma manySym (A:H.Op) (a:Keeps (Boxed X) A)(b:Keeps (Boxed X) (star A)) : Commute Q A:=by
 have e(L:H.Op)(h: Keeps (Boxed X) L): Q*(L*Q)=L*Q:=by
    ext1 x;exact starProjection_eq_self_iff.mpr (h _ (starProjection_apply_mem _ x))
 have d:star Q=Q:=isSelfAdjoint_starProjection _
 have p:=congrArg (star:H.Op→H.Op) (e _ b)
 simp only [star_mul, star_star,d, mul_assoc, e _ a] at p
 exact p.symm
lemma manyBack (A:H.Op)(a:Commute Q A): Keeps (Boxed X) A:=by
 intro y hy;apply starProjection_eq_self_iff.mp
 exact Eq.trans (DFunLike.congr_fun a.eq y) (congrArg A (starProjection_eq_self_iff.mpr hy))


open Poin Poin.Canopy
variable {ι:Type}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(Ω:H.space)
structure Fern:Prop where
 omega:Ω∈X
 warm(t:ℝ≥0):Keeps (Boxed X) (S.E t)
 space(u:Cross timeAxis):Keeps (Boxed X) (S.U u)
 pay(i:G.Chip): Keeps (Boxed X)
   (Par S (G.grade i) 1 * G.dep i * Par S (G.grade i) 1)

theorem evergreen (p:Filled S G Ω)(r: Fern X S G Ω): Dense ((span ℂ X):Set H.space):=by
 have e(t):Commute Q (S.E t):=manySym _ _ (r.warm _) ((show star _= _ from S.sym t).symm ▸ r.warm t)
 have cs:Commute Q (saucer S):= by
   ext1 x
   change Q (saucer S x)=saucer S (Q x)
   rw [saucer_apply,ship,← (Q).integral_comp_comm (cupsI ..),saucer_apply,ship]
   congr 1; funext t; unfold cups highlande; rw [ContinuousLinearMap.map_smul_of_tower]
   exact congrArg _ (DFunLike.congr_fun (e _).eq _)
 have pp:Boxed X=⊤:= p _ ⟨isClosed_closure,grown _ Ω r.omega,r.warm,r.space,?_⟩
 intro x; exact show x∈Boxed X from pp.symm ▸ (show x∈ (⊤:Submodule ℂ H.space) from mem_top)
 intro t;apply manyBack
 have er (w:G.Chip) : Keeps (Boxed X) (S.E 1 * G.dep w * S.E 1):= by
   let n:= G.grade w; let L:=Par S n 1; let R:= Cache S n
   have k:Keeps (Boxed X) R:= manyBack _ _ (cs.pow_right n)
   have m:R*L=S.E 1:=P_Heq S 1 _ zero_lt_one
   have q:=congrArg (star:H.Op→H.Op) m
   rw [star_mul, (show star L=L from parRev _ _ _ zero_lt_one),
       show star R=R from (show IsSelfAdjoint (saucer S) from saucer_sym S).pow n,
       show star (S.E 1)=_ from S.sym _] at q
   have y:S.E 1 * G.dep w * S.E 1=R * (L*G.dep w * L) * R:=by
     nth_rw 1 [←m]
     rw [←q];simp only [mul_assoc]
   rw [y]; exact fun _ p=> k _ (r.pay w _ (k _ p))
 let B:= G.dep t
 have k : Commute Q (S.E 1 * G.dep t * S.E 1):=by
   apply manySym _ _ (er _)
   rw [star_mul, star_mul, show star (S.E 1)=S.E 1 from S.sym _,←G.spar,←mul_assoc]
   exact er _
 have j : S.E 1 * (Q * B) * S.E 1= S.E 1 * (B * Q) * S.E 1:=by

   rw [←mul_assoc,(e _).eq.symm,mul_assoc,mul_assoc Q, ← mul_assoc (S.E 1) B (S.E 1), show Q*(S.E 1 * B * S.E 1)=_ from k.eq]
   rw [mul_assoc (S.E 1) (B*Q), mul_assoc B,(e _).eq]
   simp only [mul_assoc,B]
 exact show Q * B = B * Q by
   apply DFunLike.coe_injective;apply (S.whole 1).equalizer (Q*B).continuous (B*Q).continuous
   funext x;apply sub_eq_zero.mp; apply S.heat_faithful 1
   rw [map_sub];exact sub_eq_zero.mpr (DFunLike.congr_fun j x)

lemma raze (h:Dense ((span ℂ X):Set H.space)): Annihilated S X:=by
 intro v hv
 let p := (innerSL ℂ v).comp (S.E 1)
 have he:span ℂ X≤p.ker:=span_le.mpr (show ∀⦃x⦄, x∈X→p x=0 from fun {x} b=>hv x b)
 have hc:(innerSL ℂ v).ker=⊤:=by
   apply eq_top_iff.mpr;intro y _
   have w:closure ((span ℂ X):Set H.space)⊆(p.ker:Set H.space):=closure_minimal he p.isClosed_ker
   exact closure_minimal (s:=Set.range (S.E 1)) (t:=↑(innerSL ℂ v).ker) (by rintro _ ⟨x,rfl⟩;exact show p x=0 from w (h x)) (innerSL ℂ v).isClosed_ker ((S.whole 1) y)
 exact inner_self_eq_zero.mp (show v∈(innerSL ℂ v).ker from hc ▸ mem_top)
#print axioms evergreen