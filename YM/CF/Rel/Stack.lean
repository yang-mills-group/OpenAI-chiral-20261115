import YM.CF.Rel.Pupil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
def tapG(G:Gauge)(i:G.ColorIndex): G.Color→L[ℝ]ℂ:= Complex.ofRealCLM.comp (PiLp.proj _ _ i) -- tune
lemma finW(x:G.Color)(i:G.ColorIndex): tapG G i x=(x i:ℝ):=rfl
lemma time_g (P:Delph G m)(y:Fin m→G.Color): P y=∑ i:SpotG G m, (∏ j,tapG G (i j) (y j))*P (fun j=> jewelG G (i j)):=by
 have he:y=(fun i=>∑ k,(y i k:ℝ) • jewelG G k):=funext fun i=> ((EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr (y i)).symm
 conv_lhs=>rw [he]
 rw [ContinuousMultilinearMap.map_sum]; refine sum_congr rfl fun i _=> ?_; rw [P.map_smul_univ (fun j=> y j (i j))]; simp [finW,Complex.real_smul]
lemma dico(p:CurRun (m+1))(b:DialT n m)(P:Delph G (m+1))(x: InputZ G n): P (fun j=>sumH G x (diskP 0 b p j))=∑ s: SpotG G (m+1), oct p x s b 0 *P (fun j=> jewelG G (s j)):=by -- op statement taut
 conv_lhs=> rw [time_g]
 apply sum_congr rfl; intro s _; congr 1; refine prod_congr rfl fun j _=> ?_; unfold colorB; rw [finW]; rw [show diskP 0 b p j=(fillSpot b j+0,p j) from by induction j using Fin.cases <;>simp [diskP,fillSpot]]
-- shift full f representative
variable {W:KitM G n (m+1)}
abbrev vat (z:Disk n m)(P:Delph G m) : Salt n G:=fun x=>P (fun i=> sumH G x (z i))
def intoX (W:KitM G n (m+1))(k:Site n):= ∑ i:Disk n (m+1),(stroll k (-(i 0).1) (fans 0 i (W i))-fans 0 i (W i))
lemma geode {X:SpaceX G n}(h:prism (m+1) X (fun x=> ∑ p,engages W p (fun _=> x))) (k:Site n): prism (m+1) (X+intoX W k) (∑ i: Disk n (m+1),courseC k (-(i 0).1) (vat i (W i))):=by
 have he(i): prism (m+1) (fans 0 i (W i)) (vat i (W i)):=fans_p 0 i (W i)
 have hf:=prism.sumZ univ (fun i:Disk n (m+1)=> stroll k (-(i 0).1) (fans 0 i (W i))-fans 0 i (W i)) (fun i:Disk n (m+1)=>courseC k (-(i 0).1) (vat i (W i))-vat i (W i)) (fun i _=> prism.sub (prizeC k (-(i 0).1) (he i)) (he i))
 have hg:(fun x=> ∑ p, engages W p (fun _=> x))=∑ i,vat i (W i):=funext fun p=> (Finset.sum_apply p univ (fun i=>vat i (W i))).symm
 rw [hg] at h; simp only [sum_sub_distrib] at hf; have H:=prism.add h hf; rw [add_sub_cancel] at H; unfold intoX; rw [sum_sub_distrib]; exact H
lemma capi (W:KitM G n (m+1))(k:Site n)(x:InputZ G n): (∑ i: Disk n (m+1),courseC k (-(i 0).1) (vat i (W i))) x= ∑ s:SpotG G (m+1), trimU (breathL W k s) s x:=by
 rw [Finset.sum_apply,d_sum]; have he(p:Site n)(d:DialT n m)(i:CurRun (m+1)): (courseC k (-(diskP p d i 0).1) (vat (diskP p d i) (W (diskP p d i)))) x= cell k p*∑ s: SpotG G (m+1), oct i x s d 0 * W (diskP p d i) (fun j=>jewelG G (s j)):=by
    unfold courseC pulseP vat; simp_rw [sumHt]; rw [show (diskP p d i 0).1=p from rfl,cell_inverse,inv_inv]; have he(j:Fin (m+1)): ((diskP p d i j).1 + -p,(diskP p d i j).2)= diskP 0 d i j:=by induction j using Fin.cases <;> simp [diskP,add_right_comm];
    simp_rw [he]; rw [dico]
 unfold trimU; have hz(d:DialT n m)(i)(s): Ca (breathL W k s i) d=grabG W k s d i:= litZ (breathL W k s i) (fun d=>grabG W k s d i) (coins_r W k s i) d
 simp_rw [he,hz,grabG,mul_sum,sum_mul]; rw [sum_comm]; conv_rhs=> rw [sum_comm]
 refine sum_congr rfl fun i _=>?_ ; rw [sum_comm]; conv_rhs=> rw [sum_comm]
 refine sum_congr rfl fun j _=>?_ ; rw [sum_comm]; refine sum_congr rfl fun k _=> sum_congr rfl fun l _=>?_ ; ring
end YM.CF.Rel
