import YM.CF.BProof.Nerve.Circuit
import YM.CF.Cubes.Inside
import YM.CF.Cubes.Paint
import YM.Work.E01
import YM.Branch.Pick
import YM.CF.BProof.Chord
/-! Exact path estimate via a temporary axial gauge, **no choices taken into the law
from the axial gauge**; uniform local neighborhoods on every robust test. Path-order/color
choices later. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Nest
open Wilson Lattice Function Finset Gauge -- RG?
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators Classical
variable {n:Side}{s:ℕ}{G:Gauge}{u d:ℝ}
lemma nearV (x:Site n)(p:Step): separation x (x+p.vec) ≤1:= by rw [separation_comm,separation,add_comm,add_sub_cancel_right,Step.vec]; split; rw [pdist_neg]; exact pdist_step _; exact pdist_step _
lemma plank(w:Walk)(x:Site n)(y)(u:y∈ visits x w):separation x y ≤ w.length:=by
 induction w generalizing x with |nil=> simp [visits] at u; simp [u]|cons a l ih=> rcases List.mem_cons.mp u with z|h; simp [z]; exact (separation_triangle _ (x+a.vec) _).trans ((add_le_add (nearV ..) (ih _ h)).trans_eq (add_comm 1 _))
lemma prismB {A B:ℕ}(p:A≤B):Lattice.box A ⊆ Lattice.box B:= fun _ h=> box_test.mpr ⟨fun i=>by have:= (box_test.mp h).1 i; omega,fun i=>by have:= (box_test.mp h).2 i; omega⟩
lemma prism (w:Walk)(x:Cover){A:ℕ}(p:x∈Lattice.box A) (y)(h:y∈visits x w): y∈Lattice.box (A+w.length):=by
 induction w generalizing A x with |nil=> simp [visits] at h; simpa [h] using p|cons a l ih=>
    rcases List.mem_cons.mp h with z|h; rw [z]; exact prismB (by omega) p -- optional
    apply prismB _ (ih (A:=A+1) (x+a.vec) _ h); · simp only [List.length_cons]; omega
    rw [box_test]; have hm(i:Axis):(a.vec i:ℤ).natAbs ≤ 1:=by unfold Step.vec; split <;> (simp [step_apply]; split <;> simp)
    constructor <;> intro i <;> rw [Pi.add_apply] <;> first | omega | (have t₁:= (box_test.mp p).1 i; have t₂:= (box_test.mp p).2 i; have u:=hm i; omega)
private lemma trophy (r:ℕ)(δ:ℝ)(h:0<δ):∃ u:ℝ,0<u∧∀ U:Links ℤ G.El,(∀ x∈Lattice.box r,∀ i:PlaqAxes,G.chord (faceValue U (x,i))≤u)→∃ g:Cover→G.El,∀ x i,x∈Lattice.box r→x+step i∈Lattice.box r→ G.chord (Lattice.gauge g U (x,i))≤ δ:=by
 let X:=Lattice.box r; let N:= (card X:ℝ); let t:= (Fintype.card PlaqAxes:ℝ); let A:= allAxes 1; have hx : A.Nodup:= (List.nodup_finRange _).map (show Lattice.Order from 1).injective
 let K:=4*(A.length:ℝ)*(layers r).card; have he: slab r 0 A=X:=by ext w; simp only [slab_iff]; simp [A, allAxes, Axis,X]
 let q:= δ / (K*N*t+1); have hK:0≤K:=by unfold K; positivity
 have hN:0≤N:=by unfold N; positivity
 have ht:0≤t:=by unfold t; positivity
 have hp:0<q:=by unfold q; positivity
 refine ⟨q,hp,fun U W=>?_⟩
 have H:=YM.Axial.existence A r 0 U hx (center_box _); rw [he] at H; obtain ⟨p,_,p'⟩:=H
 let J:= YM.Axial.traveller A U p; let V:=Lattice.gauge J U; have hr:YM.Axial.faces X U ≤ N*(t*q):= by
   unfold YM.Axial.faces; apply (sum_le_sum (g:=fun _=>t*q) _).trans_eq (by simp [N]); intro i h; apply (sum_le_sum (g:=fun _=>q) _).trans_eq (by simp [t]); intro j _; unfold YM.Axial.face; split; exact W i h j; exact hp.le
 have hy (x i): 0≤ YM.Axial.perEdge X V x i:=by unfold YM.Axial.perEdge; split; exact chord_nonneg ..; rfl
 refine ⟨J, fun x i h k=> ?_⟩; have Hk: G.chord (V (x,i))≤ YM.Axial.edges X V:= (show G.chord (V (x,i))=YM.Axial.perEdge X V x i from (if_pos k).symm).trans_le (le_trans (single_le_sum (f:=YM.Axial.perEdge X V x) (fun i _=> hy x i) (mem_univ i)) (single_le_sum (fun i _=>sum_nonneg (fun j _=>hy i j)) h))
 have hm:q*(K*N*t+1)=δ:=div_mul_cancel₀ _ (by positivity); exact (Hk.trans p').trans ((mul_le_mul_of_nonneg_left hr hK).trans (by linarith only [hp,hm]))
lemma chord_g (V:Links ℤ G.El)(r:ℕ)(U:∀ x∈Lattice.box r,∀ i:Axis,x+step i∈Lattice.box r→ G.chord (V (x,i)) ≤ u)(x:Cover)(w:Walk)(g:∀ y∈ visits x w,y∈Lattice.box r) : G.chord (travel V x w) ≤ w.length*u:=by
 induction w generalizing x with
 | nil=> simp [travel]
 | cons a w ih=>
    let y:=x+a.vec; have hz :∀ i∈ visits y w,i∈Lattice.box r:=fun i h=>g i (List.mem_cons_of_mem x h); have he:=ih y hz; have hj:y∈Lattice.box r:=hz y (by cases w <;> simp [visits]); have hx:x∈Lattice.box r:=g x List.mem_cons_self
    have H: G.chord (a.read V x)≤ u:=by
       obtain ⟨a,b|b⟩:=a; exact U _ hx a hj; change G.chord ((negDir a).read V x)≤ _; rw [Step.neg_read, Gauge.chord_inv]; exact U _ (show x-step a∈Lattice.box r from (by simpa only [y,Step.vec,↓reduceIte,←sub_eq_add_neg] using hj)) _ (by rwa [sub_add_cancel])
    rw [travel]; exact (chord_triangle ..).trans ((add_le_add H he).trans_eq (by rw [List.length_cons]; push_cast; ring))
abbrev Clear (u:ℝ)(r:ℕ)(U:Config G n)(x:Site n): Prop:=Disjoint (RG.flags u U) (region n x r)
structure Law (G:Gauge)(u δ:ℝ)(r:ℕ):Prop where
  gain{n:Side}(x:Site n)(U:Config G n): Clear u r U x→∀ p q:Walk, stop (0:Cover) p=stop (0:Cover) q→ p.length≤r → q.length≤r → cd G (travel U x p) (travel U x q)≤ δ
-- cost
lemma register(G:Gauge)(δ:ℝ)(h:0<δ)(r:ℕ)(M:ℝ)(v:0<M): ∃ u:ℝ,0<u∧u≤ M∧Law G u δ r:=by
 let e:=δ/(2*r+1); have he: 0<e:= by unfold e; positivity
 obtain ⟨u,hu,H⟩:= trophy (G:=G) r e he; refine ⟨min u M,lt_min hu v,min_le_right ..,⟨fun {n} x U W p q m hP hQ=>?_⟩⟩ -- tune law ctor
 let V:= expandAt x U; have he': ∀ z∈Lattice.box r,∀ i:PlaqAxes,G.chord (faceValue V (z,i)) ≤ u:=by
    intro z hz i; let y:=wrap n z+x; unfold V faceValue; rw [travel_at]; apply le_trans (b:=min u M) _ (min_le_left ..); by_contra! hu; let D: Lattice.Face (Per n):=(y,i); have ht: y ∈ RG.flags (min u M) U:=RG.flags_spec ..|>.2 ⟨D, Work.E01.base_touched D,hu⟩; apply Finset.disjoint_left.mp W ht; apply (reg_in ..).2; unfold y; rw [separation_comm, separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le hz
 obtain ⟨g,l⟩:= H V he'; let Y:=Lattice.gauge g V
 have hk(p:Walk)(u:p.length≤r):cd G 1 (travel Y 0 p) ≤ r*e:= by rw [cd_one]; apply (chord_g Y r (fun x h i=>l x i h) 0 p (fun x h=>prismB (show 0+p.length≤r from (by omega)) (prism p _ (center_box 0) _ h))).trans; gcongr
 have hx(p:Walk): travel Y 0 p= g 0 * travel U x p * (g (stop 0 p))⁻¹:=by unfold Y V; rw [travel_gauge,travel_at]; simp
 have hp':= cd_triangle G (travel Y 0 p) 1 (travel Y 0 q); apply le_trans (b:=cd G (travel Y 0 p) (travel Y 0 q)) _ (hp'.trans _)
 · rw [hx,hx,m,cd_mul_right,cd_mul_left]
 rw [cd_symm]; have hr:e*(2*r+1)=δ:=div_mul_cancel₀ _ (by positivity); linarith only [hr,hk p hP,hk q hQ,he]
end YM.CF.BProof.Mesh.Nest
