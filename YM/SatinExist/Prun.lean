import YM.SatinExist.Isthar
import YM.SatinExist.Cecily
/-!
 # Joint fields continuation. Pulse IBP in gap coordinates.
-/
set_option autoImplicit false
set_option maxRecDepth 2450
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "E" => elast S
local notation "D" => Bench S
local notation "K" => Cache S
local notation "R" => saucer S
local notation "T" => M S
variable (x:H){n:ℕ}(p:E4)
variable (F G:Fin n→H.Op)
abbrev lineC (i:Fin n)(w:E4)(y:Fin n→E4)(k:Fin n):= if i ≤ k then y k+w else y k
lemma all_after (w:E4)(y:Fin n→E4): regiaN S x n F G (p+w) (fun i=> y i+w)= regiaN S x n F G p y:=by
 induction n generalizing p with
 | zero=>rfl
 | succ n ih=> rw [regiaN,regiaN]; let Z(k:Fin n):=y k.succ+w; rw [add_sub_add_right_eq_sub]; change T _ (F 0 (G 0 (regiaN S x n _ _ _ Z)))= _; rw [show Z=(fun i=>Fin.tail y i+w) from rfl,ih]
variable (y:Fin n→E4) (i:Fin n)
abbrev badge (i:Fin n)(m:H.Op):= update F i (m*F i)
local notation "J" i:max M:max=> badge F i M
lemma ref_i : HasDerivAt (fun s:ℝ=> regiaN S x n (J i (R)) G p (lineC i (s • basis j) y))
    (I • (regiaN S x n F G p y - regiaN S x n (J i (R)) G p y)) 0:=by
 induction n generalizing p with
 | zero=> exact i.elim0
 | succ n ih=>
   refine Fin.cases ?_ (fun i=>?_) i
   · let H':= Fin.tail G; let F':=Fin.tail F; let Y':= Fin.tail y; let a:=y 0; let t:= regiaN S x n F' H' a Y'; let A:= a-p; let m:H:=F 0 (G 0 t); let B:= T A; let W':= badge F 0 R
     have hp:Fin.tail W'= F':=funext (fun i=> update_of_ne (Fin.succ_ne_zero i) _ _); have hk:W' 0= R*F 0:= update_self ..
     let δ(s:ℝ):= S.edge s (R m)
     have ht: HasDerivAt δ (I • (m-R m)) 0:= by
       convert fanfare S m 0 using 1; unfold parade; rw [S.birth]; rfl
     let f(s:ℝ):= B (δ s); have hv:HasDerivAt f (B (I • (m-R m))) 0:= (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ ht
     change HasDerivAt _ (I • (_ - regiaN S x (n+1) W' G p y)) _; rw [regiaN,regiaN,hk,hp] -- check only derivative RHS? rw matches L
     apply HasDerivAt.congr_deriv (hv.congr_of_eventuallyEq ?_) ?_ -- reorder
     · apply Eventually.of_forall; intro s; let w:= s • basis j; let k:= lineC (0:Fin (n+1)) w y; change regiaN S x (n+1) W' G p k = _; have he:k=fun i=> y i+w:= funext fun i=> if_pos (Fin.zero_le _); rw [regiaN,hk,hp,he]; change T (a+w-p) ((R*F 0) (G 0 (regiaN S x n F' H' (a+w) (fun i=> Y' i+w))))= _; rw [all_after,show a+w-p=A+w from (by unfold A; abel),← tgo,timeslot]; rfl
     · rw [map_smul,map_sub]; change I • (B m-B (R m))=_; rfl
   · let t:Fin n:= i; let A:= badge F (Fin.succ t) (R); let f:=lineC (Fin.succ t); have hp:A 0=F 0:= update_of_ne (Fin.succ_ne_zero t).symm _ _
     have ht:Fin.tail A= badge (Fin.tail F) t R:= by
        ext1 k; rcases eq_or_ne k t with e|e
        · subst k; simp only [Fin.tail, A,badge,update_self]
        · change A k.succ= _; unfold A badge; rw [update_of_ne,update_of_ne]; exacts [rfl,e,fun h=> e (Fin.succ_injective _ h)] -- indentation
     let g(i:ℝ):= f (i•basis j) y; have he(s:ℝ):g s 0=y 0:= if_neg (not_le.mpr (Fin.succ_pos t)); have hv(s:ℝ): Fin.tail (g s)=lineC t (s • basis j) (Fin.tail y):= by ext1 i; simp only [g,f, Fin.tail,lineC,Fin.succ_le_succ_iff]
     let B:=T (y 0-p)*F 0* G 0
     have d:= ((B.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt _ (ih (y 0) (Fin.tail F) (Fin.tail G) (Fin.tail y) t)
     change HasDerivAt (fun i:ℝ=> regiaN S x (n+1) A G p (g i)) (I •( regiaN S x (n+1) F G p y - regiaN S x (n+1) A G p y)) _; simp_rw [regiaN, hp,ht,he,hv]
     apply HasDerivAt.congr_deriv d; dsimp only [ContinuousLinearMap.coe_restrictScalars']; rw [map_smul,map_sub]; rfl -- exact.Composition
abbrev stepAfter (j:Axis)(i:Fin n):Points n:= WithLp.toLp _ (fun k=> if i ≤ k then basis j else 0)
variable (f:Joint n)
def shed (j:Axis)(i:Fin n):= lineDerivOpCLM ℂ (Joint n) (stepAfter j i)
abbrev penny (j:Axis)(i:Fin n) : Joint n →L[ℂ] Joint n:= ContinuousLinearMap.id ℂ _ + I • shed j i
lemma badge_one : wishL S x p F G f = wishL S x p (badge F i R) G (penny j i f):=by
 let U:=regia S x p F G
 let V:=regia S x p (J i (R)) G; let D':= fun q=> I • (U q- V q)
 have h(q:Points n):HasLineDerivAt ℝ V (D' q) q (stepAfter j i):=by
    apply (ref_i S x p F G q.ofLp i).congr_of_eventuallyEq; refine Eventually.of_forall fun s=>?_
    change regiaN S x n _ G p (WithLp.ofLp (_:Points n))= _; congr 1; ext1 k; by_cases g:i≤ k <;> simp [lineC,stepAfter,g] -- simpl
 have v(q:Points n):HasLineDerivAt ℝ f (shed j i f q) q (stepAfter j i):= (f.hasFDerivAt _).hasLineDerivAt _
 have ht: (fun q=> f q • D' q)= (fun q=> I • (f q • U q - f q • V q)):= funext fun s=>by unfold D'; rw [smul_comm, smul_sub]
 have he:Integrable (fun q=> f q • D' q):= by rw [ht]; exact ((regiaI S x p F G f).sub (regiaI ..)).smul _
 have hp: (∫ q, f q • D' q)= - (∫ q,shed j i f q • V q):= integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (B:=ContinuousLinearMap.lsmul ℝ ℂ) (regiaI ..) he (regiaI ..) (fun q _=> v q) (fun q _=> h q)
 let X:= wishL S x p (badge F i R) G; let Q:= wishL S x p F G f; rw [ht, integral_smul,integral_sub (regiaI ..) (regiaI ..)] at hp; rw [show penny j i f=f+I • shed j i f from rfl,map_add,map_smul]; change I • (Q-X f) = -X (shed j i f) at hp; have he:=congrArg (-I • ·) hp
 have ht: (-I) * I=1:=by rw [neg_mul,I_mul_I,neg_neg]
 rw [smul_smul,ht,one_smul,neg_smul,smul_neg,neg_neg] at he; exact (sub_eq_iff_eq_add'.mp he)
end YM.SatinJets
