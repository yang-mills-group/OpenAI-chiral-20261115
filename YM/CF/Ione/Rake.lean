import YM.CF.Salt.Dial
import YM.CF.Vow.Face
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Ione
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
private lemma seat(x:Bool):(crib V t (x.xor r)).val * windX (c.xor t) (crib U r x).val=feeJ r (t.xor c) • (crib (V*whiten c U) (r.xor t) x).val :=by
 cases r <;> cases c<;> cases t <;>cases x <;> simp [feeJ,crib, Pastry.thread,whiten,windX, ccU, filmG, Matrix.smul_mul,Matrix.mul_smul,smul_smul, cc_mul,cc_smul]
abbrev f_sound(U:UNI n)(r x:Bool)(i:n):=∑ j:n, (crib U r x).val j i • put (x.xor r,j)
lemma L_mile (x: Bool)(i:n): lotY b r U (put (x,i))=f_sound U r x i:=by
 rw [Urn.mold]; unfold roseB; rw [Fintype.sum_prod_type,sum_eq_single (x.xor r)]; apply sum_congr rfl; intro i _; unfold sewV; rw [Urn.cream,if_pos rfl]; intro a _ p; apply sum_eq_zero; intro i _; unfold sewV; rw [Urn.cream,if_neg p,zero_smul]; simp
lemma G_lot (z:ℂ)(A:FC (LeanV n)):lotY b r U (z • A)=cSignX (b.xor r) z • lotY b r U A:=lonY b r U A z
lemma honey (x:Bool)(i:n):lotY c t V (lotY b r U (put (x,i)))=feeJ r (t.xor c) • lotY (b.xor c) (r.xor t) (V*whiten c U) (put (x,i)):=by
 rw [L_mile,L_mile]; unfold f_sound; rw [map_sum]; simp_rw [G_lot,L_mile]; unfold f_sound; rw [Finset.smul_sum]; simp_rw [Finset.smul_sum, smul_smul,Bool.xor_assoc]; rw [sum_comm]; apply sum_congr rfl; intro j _; rw [← sum_smul]; apply congrArg (fun p:ℂ=> p • _); have he:=Matrix.ext_iff.mpr (seat (n:=n) r t c U V x) j i; rw [Matrix.smul_apply,Matrix.mul_apply,smul_eq_mul] at he; rw [← show ∑ k:n, (crib V t (x.xor r)).val j k * (windX (c.xor t) (crib U r x).val) k i= _ from he]; exact sum_congr rfl fun k _=>by rw [mul_comm]; cases c.xor t<;> rfl -- tune
lemma hiB (A:ribbon n): paintR c t V (paintR b r U A) = paintR (b.xor c) (r.xor t) (V*whiten c U) A:=by
 apply Subtype.ext; let f:=cSignX ((b.xor c).xor (r.xor t)); apply Salt.ruler ((lotY c t V).comp (lotY b r U)) (lotY (b.xor c) (r.xor t) (V*whiten c U)) (feeJ r (t.xor c)) (by unfold feeJ; split<;> ring) (fun ⟨x,y⟩=>Ione.honey b r t c U V x y) f _ (fun i j=>G_lot ..) A.val ((fresh_p (fineShape A)).rise (Set.subset_univ _)) -- P infer
 intro i P; rw [RingHom.comp_apply,G_lot,G_lot,RingHom.comp_apply]; congr 1; cases b <;> cases c<;> cases r<;>cases t<;>simp only [f,Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.not_false,cSignX]; all_goals simp
-- up
open Nacre
variable {N:Side} (s t:Sweep N)
def glowT (b:Bool)(a:Shape):=paintR b (detX a.s) (siteU a b (spinU b a.s) N) -- implicit N?
abbrev suit_Y (q:Sweep N) : Cipher N →ₐ[ℝ] Cipher N:= paintR q.charge (detX q.s) (siteU (castX q) q.charge (spinU q.charge q.s) N)
lemma glowP (a:Shape)(X:Cipher N)(V:UNI SpinIdx)(h:JetS a.s b (detX a.s) V): paintR b (detX a.s) (siteU a b V N) X= glowT (N:=N) b a X:=by obtain ⟨z,p,t,w⟩:= Hive.king b _ V _ h (spinZ ..); exact spin_k _ _ _ (Ygs _ _ _ p) t w _
lemma tama (q:Sweep N)(u:UNI SpinIdx)(t:JetS q.s q.charge (detX q.s) u) (X:Cipher N) : FrameR q u X=suit_Y q X:= glowP q.charge (castX q) X u t
lemma tyga(a d:Shape)(X:Cipher N): glowT (N:=N) c d (glowT b a X)= glowT (N:=N) (b.xor c) (joinX a d) X:=by
 let U:=spinU b a.s; let V:=spinU c d.s; let Q:=V*whiten c U; unfold glowT; rw [hiB,Levier.turns,←det_p]; exact glowP (b.xor c) _ X Q (shineU b a c U V _ (spinZ ..) (spinZ ..))
lemma canP (Y:Shape)(X:Cipher N): glowT (N:=N) b (castX (Levier.ray (N:=N) b Y)) X= glowT b Y X:=by
 let t:=wrap N Y.t; let z:= fee (Rush.periods N (lift t)-Rush.periods N Y.t); refine spin_k _ _ _ (z:=z) (utu N b (spinU b Y.s) Y.s (Lattice.lift t) Y.t (wrap_lift _)) ?_ (fee_real _) X; exact (pow_two _).trans (fee_one _)
lemma moon_Y(X:Cipher N): suit_Y t (suit_Y s X)=suit_Y (s*t) X:=by
 change glowT t.charge (castX t) (glowT s.charge _ X)= glowT (s*t).charge (castX (s*t)) X; rw [tyga]; let a:=castX s; let v:=castX t; rw [show (s*t).charge=s.charge.xor t.charge from rfl]; have ht:s*t=Levier.ray (s.charge.xor t.charge) (joinX a v):=by rw [←ray_join,show ray s.charge a=s from ray_i s,show ray t.charge v=t from ray_i t]; -- tune
 rw [ht,canP]
lemma paint_in (W:UNI n): Injective (paintR false false W):=by
 intro i j p; refine Subtype.ext ?_; let V:= quantU (n:=LeanV n) (spice W false); have h: twist (n:=Finset (LeanV n)) V i.val=twist (n:=Finset (LeanV n)) V j.val :=congr_arg (fun i:ribbon n=> i.val) p
 exact (twist V).injective h
lemma toon_Q(A:Cipher N): suit_Y 1 A=A:=by
 suffices h:Injective (suit_Y (N:=N) 1) from h (by rw [moon_Y 1 1 A,one_mul])
 unfold suit_Y; rw [show detX (1:Sweep N).s=false from det_i]; exact paint_in _ -- tune
lemma boom_Q (g:Site (More N)→E)(X:Cipher N): suit_Y s (paintR false false (tradew N g) X) = paintR false false (tradew N ((polarT s.charge ∘g) ∘ (castX s).anon N)) (suit_Y s X):=by
 unfold suit_Y; rw [hiB,hiB,tr_s]; simp only [site_ui,Bool.false_xor,Bool.xor_false,whiten,Bool.false_eq_true,↓reduceIte,envoy] -- tune
end YM.CF.Ione
