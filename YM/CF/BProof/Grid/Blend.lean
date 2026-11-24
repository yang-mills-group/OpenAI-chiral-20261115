import YM.CF.BProof.Grid.Poke
import YM.CF.BProof.Grid.Mean
import YM.CF.BProof.Grid.Buy

/-! One dyadic averaging step. Use corner paths via the first corner of the smallest
entity. (They stay in the entity.) -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Blend
open Function Lattice Entity MeasureTheory
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable (G : Gauge) {n : ℕ} {c s : Side}(g : Ratio c s)(U : Wire G n s)
local notation "M" => G.mat
variable (q : Floor G.El n c)

def book (x:Cubic n s)(b:Dice n) : G.El := let p:=chief g x; let A:=p.paths G g U; q (eighth g x b)*(A (node8 g x b))⁻¹*A x

def blend (x:Cubic n s) := closest G (average (M ∘ book G g U q x))

local instance : MeasurableSpace G.Mat:=borel _
local instance : BorelSpace G.Mat:=⟨rfl⟩
lemma birth_m : Measurable (uncurry (blend G g (n:=n))):=by
 apply measurable_pi_lambda
 intro x; let A:= Wire G n s× Floor G.El n c; let B(b : Dice n) (p : A):= M (book G g p.1 p.2 x b); change Measurable (closest G ∘ fun p : A=>average (fun b=> B b p)); have hm : Measurable (closest G):=closest_m G; apply hm.comp; apply Continuous.measurable; refine mean_c _ (fun i=>?_)
 change Continuous (G.mat ∘ fun p : Wire G n s × Floor G.El n c=> book G g p.1 p.2 x i)
 apply G.continuous_mat.comp; unfold book paths; dsimp only; fun_prop

lemma pinned (x:Cubic n c) : blend G g U q (grow g x)=q x:=by
 have he:book G g U q (grow g x)=Function.const _ (q x):=by ext1 i; simp [book,node8,facing]
 unfold blend; rw [he,show M ∘ (Function.const (Dice n) (q x))=fun _:Dice n=> M (q x) from rfl,average_const]; exact (nearest_all_same ..).mp (closest_p G _)

-- work in a common higher-entity coordinate.
def shelf (p:Entity n c)(x:Cubic n c):= q x*(p.paths G g U (grow g x))⁻¹
abbrev shifted (p:Entity n c)(x:Cubic n s):=fun i=> book G g U q x i * (p.paths G g U x)⁻¹
variable (p:Entity n c) (hc:4≤c.val)(t:g.count.val=2){m α:ℝ}(hm:0≤m)(H: Wire.Flat G U Set.univ m)
include hc t H hm
lemma shared (w : Entity n c)(h:w.Under p)(x:Cubic n s)(hx:w.Mem g x)(y:Cubic n s)(hy:w.Mem g y):
    let F(v):= w.paths G g U v * (p.paths G g U v)⁻¹; cd G (F x) (F y) ≤ 16*(n:ℝ)^2*m := by
 intro F; have hu:cd G (F x) (F y) ≤ (4*n*m)*steps x y:=w.bound_of_step g (cd G) F (cd_self G) (cd_symm G) (cd_triangle G) (fun x i hx h' => ?_) hc hx hy -- tune obtain goals
 have ht:=w.small_metric g x y hx hy; rw [t] at ht
 exact hu.trans ((mul_le_mul_of_nonneg_left (by exact_mod_cast ht : (steps x y:ℝ)≤ (↑(n*(2*2)):ℝ)) (by positivity)).trans (by push_cast; exact le_of_eq (by ring)))
 let A:=w.paths G g U; let B:=p.paths G g U; let y:=slide x i; let v:=U (x,i)
 have hw:= w.smooth G g U hx h' hc hm (fun x i j _ _ _ _=>H x i j trivial trivial trivial trivial); have hp:= p.smooth G g U (h.sites g hc hx) (h.sites g hc h') hc hm (fun x i j _ _ _ _=>H x i j trivial trivial trivial trivial);
 change cd G (A x*(B x)⁻¹) _ ≤ _; rw [show A x*(B x)⁻¹=A x*v*(B x*v)⁻¹ by group]; apply le_trans (cd_perturb G (A x*v) ((B x*v)⁻¹) (A y) (B y)⁻¹); rw [cd_inv]; exact (add_le_add hw hp).trans (by rw [t]; push_cast; exact le_of_eq (by ring))

lemma translated (x:Cubic n s)(hx:p.Mem g x)(b:Dice n): cd G (shifted G g U q p x b) (shelf G g U q p (eighth g x b))≤ 16*(n:ℝ)^2*m := by
 let w:=chief g x; let y:=node8 g x b; let A:=w.paths G g U; let B:=p.paths G g U; let K:=q (eighth g x b)
 have he := zero_proper g hc x
 have hw:= shared G g U p hc t hm H w (chief_sub g p hc x hx) x he.1 y (placed g w hc x b he.1) -- tune
 change cd G (K*(A y)⁻¹*A x*(B x)⁻¹) (K*(B y)⁻¹) ≤ _
 rw [mul_assoc,mul_assoc,cd_mul_left,← cd_mul_left G (A y),show A y*_ =A x*(B x)⁻¹ from by group]; exact hw

lemma tide {x:Cubic n c}(hx:p.Mem (digit c) x)(i)(hu:p.Mem (digit c) (slide x i))(hh: SeatBound G q (Wire.long G U g) α):
    cd G (shelf G g U q p x) (shelf G g U q p (slide x i)) ≤ α + 4*n*m := by
 let A:=p.paths G g U; let y:=grow g x; let z:=slide y i; let w:= slide x i; let V:=grow g w
 have ht:=midpoint g p x i hc t hx hu
 have hp : V=slide z i:=by rw [show V=jump y i g.count.val from grow_step ..,t,show 2=1+1 from rfl,jump_succ,jump_one]
 have hZ:= (dimension g p w).mpr hu
 let L:= Wire.long G U g (x,i)
 have hl : L=U (y,i)*U (z,i):=by unfold L Wire.long; rw [t, show (2:ℕ)=1+1 from rfl, Wire.line]; dsimp only; rw [Wire.line_one,jump_one]
 have smooth x i (h:p.Mem g x)(u:p.Mem g (slide x i)):= p.smooth G g U h u hc hm (fun x i j _ _ _ _=>H x i j trivial trivial trivial trivial)
 have he:cd G (A y*L) (A V) ≤ 4*n*m:=by
   rw [hl, ← mul_assoc]; apply le_trans (cd_triangle G _ (A z* U (z,i)) _); rw [cd_mul_right]; refine (add_le_add (smooth _ _ ((dimension ..).2 hx) ht) (show cd G (A z*_) _ ≤_ from hp.symm ▸ smooth _ _ ht (hp ▸ (show p.Mem g V from hZ)))).trans ?_ -- tune
   · rw [t]; push_cast; exact le_of_eq (by ring)
 change cd G (q x*(A y)⁻¹) (q w*(A V)⁻¹)≤ _; rw [show q x*(A y)⁻¹=q x*L*(A y*L)⁻¹ by group]
 exact (cd_perturb ..).trans (add_le_add (hh x i) ((cd_inv ..).trans_le he))

lemma fares (hh: SeatBound G q (Wire.long G U g) α)(ha:0≤α) (x:Cubic n s)(hx:p.Mem g x):
    let D := 16*n^2*m; let L:=α+4*n*m; ∀ b, cd G (shelf G g U q p p.home) (shifted G g U q p x b) ≤ D+L*(2*n):= by
 intro D L b; have hY: p.Mem (digit c) p.home:= by simpa only [first,digit_grow] using p.mem_first (digit c)
 have hv : p.Mem (digit c) (eighth g x b):= (dimension g ..).mp (placed g p hc x b hx)
 apply le_trans (cd_triangle G _ (shelf G g U q p (eighth g x b)) _); rw [cd_symm G (shelf _ _ _ _ p (eighth _ _ _)),add_comm D]
 refine add_le_add (le_trans (p.bound_of_step (digit c) (cd G) (shelf G g U q p) (δ:=L) (cd_self G) (cd_symm G) (cd_triangle G) (fun x i h u=> tide G g U q p hc t hm H h i u hh) hc hY hv) ?_) (translated G g U q p hc t hm H x hx b)
 apply mul_le_mul_of_nonneg_left
 · have ht:= p.small_metric (digit c) p.home _ hY hv; rw [digit_count,mul_one,Nat.mul_comm] at ht; exact_mod_cast ht
 unfold L; positivity
end YM.CF.BProof.Grid.Blend
