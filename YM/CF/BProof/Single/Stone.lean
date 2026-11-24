import YM.CF.Dial.Pry
import YM.CF.Tulip.Metro
import YM.CF.BProof.Site.Micro
import YM.CF.BProof.Single.Coat
import YM.CF.BProof.Stint.Global
/-! Single-stage for VolB-op. Gauge covariance under *any* witness in admissible
hypotheses. Use Lipschitz pay in sum-distance (at most linear in support size times
max-distance of B-gate). Distinguish fields (true fields may be outside guard, here
U is the *repaired argument* on which all operators taken, *before* substitutions.) -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {s N : Side}{a d :ℝ}{D:Type}
lemma grove_loc {S: Seal (Site s)}(h:Grove (terr s) S): Micro.Loc S:= fun i p j q=>rooted h i p j q
abbrev Counter (s : Side)(a:ℝ):= { U:Bkg s // Guard U a }
def skin (s:Side)(a:ℝ) (u:Site s→E)(U: Counter s a): Counter s a:=⟨gauge u U.val,U.property.cov u⟩
abbrev fa (x y : Bkg s) (S: Seal (Site s)) := fare S (profile x) (profile y)
abbrev badgeOf (i: Single N) := node i.1.1
def quarry (N : Side) (a d:ℝ) : Stage (Site (More N)) (Single N) (Counter (More N) d) (Geometry N) where
 F:= terr (More N)
 home:= badgeOf
 drive:= skin (More N) d
 eval S x y:=fa x.val y.val S/ |a|
 pos S x y:= div_nonneg (fare_t ..) (abs_nonneg _)
 includeV h x y:= div_le_div_of_nonneg_right (fare_inc h _ _) (abs_nonneg _)
lemma quota_p : 0< Tenant.quota:= lt_of_lt_of_le (by norm_num) quota_bound
structure Feet (N :Side) (D:Type) where
 st : Stage (Site (More N)) (Single N) D (Geometry N)
 town : st.F=terr (More N)
 index : st.home=badgeOf
namespace Feet
variable (b:Feet N D)
def mark : Tag b.st:=⟨tradew N,fun g i j t=> (bail N 1).keeps g i j (by rw [b.index] at t; exact t)⟩
theorem cap : Capacity b.st quota:=by
 refine ⟨?_,?_,?_⟩ <;> intro i j <;> rw [b.town]
 · exact Tenant.glen ..
 · exact (meterQ N 1).ball i j
 rw [show board b.st _= _ from (by unfold board; rw [b.index]; rfl : board b.st (bay (terr (More N)) i j)=board (forum N 1) (bay (terr (More N)) i j))]; exact (meterQ N 1).place i j -- tune
end Feet
def iron (N : Side)(a d:ℝ) : Feet N (Counter (More N) d):= ⟨quarry N a d,rfl,rfl⟩
theorem drill {A : Chin N→Op (Single N)}{k: Pay}(p:Solo k.rate k.cash A a)(h:0<a)(v:d≤a): Earn k (iron N a d).mark (iron N a d).mark (fun x=> A (profile x.val)):=by
 let ρ(i:Counter (More N) d):Openc (More N) a:=⟨profile i.val,i.val,i.property.shrink v,by simpa⟩; have ht: Continuous ρ:= Continuous.subtype_mk (profile_c.comp continuous_subtype_val) _
 apply Earn.restrict (s:=bail N a) (t:=bail N a) (A:=fun x=>A x.val) p.lib ρ ht rfl rfl (fun S x y=>le_rfl) id ?_ rfl rfl; intro g y; exact Subtype.ext (profile_g g _).symm
lemma fa_total (S:Seal (Site s))(U V:Bkg s): fa U V S= ∑ i ∈ leaks S, scenery (U i) (V i):=by
 refine sum_congr rfl fun i _=>?_ ; unfold scenery; let Q(p q:Twig):=‖p-q‖; apply le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_) _
 · intro b; cases b; simp only [profile,Bool.false_eq_true,ite_false,Pi.sub_apply]; rw [←star_sub,norm_star]; exact le_rfl
 exact norm_le_pi_norm (profile U i-profile V i) true
lemma leak_cap (S:Seal (Site s)): ((leaks S).card:ℝ) ≤ S.card*4 := by
 have hv : (leaks S).card ≤ (S ×ˢ (univ:Finset Axis)).card:= card_le_card (fun i h=> mem_product.mpr ⟨(mem_filter.mp h).2.1,mem_univ _⟩)
 rw [card_product,card_univ,show Fintype.card Axis=4 from Fintype.card_fin _] at hv; exact_mod_cast hv
lemma leaks_up {S T:Seal (Site s)}(h:S⊆T): leaks S ⊆ leaks T:= fun i g=>mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp g).2.1,h (mem_filter.mp g).2.2⟩
lemma fa_bound {S:Seal (Site s)}{t:ℝ}(p:0≤t){U V:Bkg s}(h:∀ i∈leaks S,scenery (U i) (V i)≤t): fa U V S≤ S.card*4*t:=by
 rw [fa_total]; exact le_trans (sum_le_sum h) (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (leak_cap _) p)
lemma fa_bay {z: Site s}{w:ℕ}{t:ℝ}(p:0≤t){U V:Bkg s}(h:∀ i∈leaks (bay (terr s) z w), scenery (U i) (V i)≤t): fa U V (bay (terr s) z w)≤16*((w:ℝ)+1)^4*4*t:= (fa_bound p h).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Tenant.reach ..) (by norm_num)) p)
end YM.CF.BProof.Spin
