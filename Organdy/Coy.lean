import Organdy.Aquatic
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)

open Hive

section
variable (b r t j:Bool)(U V:UNI (Single n))
lemma uniformP (S R:Fz→+*Fz)(z:ℂ)(u:star z=z)(g:∀ i: Dwell n,S (put i)=z • R (put i))
  (s:∀ w,S (star w)=star (S w))(t:∀ w,R (star w)=star (R w))(x:Hake.Oboe (Dwell n)):
   S (bell x)=z • R (bell x):=by
 rcases x with ⟨_|_,i⟩; swap; · exact g i
 change S (star (put i))=z • R (star (put i))
 rw [s,t,g,star_smul,u]

lemma spicy (A:Fz)(p:Keys A):
  lotY j t V (lotY b r U A)=lotY (b.xor j) (r.xor t) (V*whiten j U) A:=by
  let c:=(b.xor j).xor (r.xor t)
  let z:=feeJ r (t.xor j)
  have u:star z=z:=by unfold z feeJ; split<;>simp
  refine Hive.kin ((lotY j t V).comp (lotY b r U)) _ z
   (by unfold z feeJ;split<;>ring) (uniformP _ _ z u
    (fun ⟨x,y⟩=> Ione.honey b r t j U V x y)
    (fun w=>by rw [RingHom.comp_apply,sweet,sweet];rfl) (sweet _ _ _)) (cSignX c) ?_ (fun i j=>G_lot ..) A p
  intro x B;rw [RingHom.comp_apply,G_lot,G_lot,RingHom.comp_apply]
  congr 1
  cases b <;>cases r <;> cases t <;> cases j <;> simp [c,cSignX]

lemma spiceRoot {z:ℂ}(e:U.val=z • V.val)(g:z^2=1)(u:star z=z)
 (A:Fz)(p: Keys A) :
 lotY b r U A=lotY b r V A:=by
 have he(i:Dwell n): lotY b r U (put i)=z • lotY b r V (put i):=by
   rcases i with ⟨x,i⟩
   rw [L_mile,L_mile]; unfold f_sound
   rw [Finset.smul_sum]; refine sum_congr rfl fun k _=>?_
   have h:(crib U r x).val=z • (crib V r x).val:=by
     cases x <;> cases r<;> simp only [crib, Pastry.thread] <;> simp [filmG,ccU,e,cc_smul,u,smul_comm z]
   rw [h,Matrix.smul_apply,smul_eq_mul,smul_smul]
 exact Hive.kin _ _ z g (uniformP _ _ z u he (sweet _ _ _) (sweet _ _ _)) (cSignX (b.xor r)) (G_lot b r _) (G_lot b r _) _ p

lemma spiceW (x:Shape) (X Y:UNI SpinIdx)(A:Fz)(p: Keys A)(i:JetS x.s b (detX x.s) X)
 (g: JetS x.s b (detX x.s) Y):
 lotY b (detX x.s) (siteU x b X n) A=lotY b (detX x.s) (siteU x b Y n) A:=by
 obtain ⟨z,t,u,k⟩:=king b _ X Y i g; exact spiceRoot b _ _ _ (Ygs _ _ _ t) u k A p

variable (X:FC (Dwell n))(k: Keys X)
local notation "⚝" c:max x:max y:max=> lotY c (detX (x).s) (siteU x c (spinU c (x).s) n) y
include k

lemma pushZ (a d:Shape): ⚝ j d (⚝ b a X)= ⚝ (b.xor j) (joinX a d) X:=by
 let U:=spinU b a.s; let V:=spinU j d.s
 rw [spicy _ _ _ _ _ _ X k,Levier.turns,←det_p]
 exact spiceW (b.xor j) _ _ _ X k (shineU b a j U V _ (spinZ ..) (spinZ ..)) (spinZ ..)
lemma pushR (Y:Shape): ⚝ b (castX (Levier.ray (N:=n) b Y)) X=⚝ b Y X:=by
 let t:=wrap n Y.t; let z:=fee (Rush.periods n (Lattice.lift t)-Rush.periods n Y.t)
 refine spiceRoot b (detX Y.s) _ _ (z:=z) (utu n b (spinU b Y.s) Y.s (Lattice.lift t) Y.t (wrap_lift _)) ?_ (fee_real _) X k
 exact (pow_two _).trans (fee_one _)

lemma twice (tq:Sweep n):roll tq (roll s X)=roll (s*tq) X:=by
 change ⚝ (tq.charge) (castX tq) (⚝ B₁ (castX s) X)=⚝ ((s*tq).charge) (castX (s*tq)) X
 rw [pushZ s.charge tq.charge X k]; let a:=castX s; let v:=castX tq
 rw [show (s*tq).charge=s.charge.xor tq.charge from rfl]
 have ht:s*tq=Levier.ray (s.charge.xor tq.charge) (joinX a v):=by
    rw [←ray_join,show ray s.charge a=s from ray_i s,show ray tq.charge v=tq from ray_i tq]
 rw [ht,pushR _ X k]
end

variable (t:Sweep n)

abbrev stale (V:Bag n):Prop :=∀ i z,Keys (V i z)
lemma wheel (V:Bag n)(X:Aura n)(z:Orbit n): whirlB s V (moldA s X) (yellA s z)=roll s (V X z):=by
 change roll _ (V ((moldA s).symm _) _)=_
 rw [Equiv.symm_apply_apply,toback]

lemma spinning (X:Bag n)(p:stale X):whirlB t (whirlB s X)=whirlB (s*t) X:=by
 funext j y; obtain ⟨a,rfl⟩:=(moldA (s*t)).surjective j
 obtain ⟨x,h⟩:∃ x,y=yellA (s*t) x:=⟨_,(outback _ y).symm⟩
 rw [h,wheel,←yell_t,←hush_k,wheel,wheel]
 exact twice s _ (p _ _) _

lemma inject_1 : Injective (whirlB (1:Sweep n)):=by
 intro p q k
 funext i v
 have ht:=congr_fun (congr_fun k (moldA 1 i)) (yellA 1 v)
 rw [wheel,wheel] at ht
 have h :detX (1:Sweep n).s=false:=det_i
 unfold roll at ht;rw [h] at ht
 exact (twist _).injective ht
lemma unspun (X:Bag n)(p:stale X):whirlB 1 X=X:= inject_1 (by rw [spinning 1 1 X p,one_mul])
