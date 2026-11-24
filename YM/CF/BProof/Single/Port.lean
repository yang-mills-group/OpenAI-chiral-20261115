import YM.CF.BProof.Single.Realm
/-! Augment admissible argument domain, e.g. keeping projection bits, paint. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint SU.Pair
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{D D' Z:Type}
namespace Feet
def double (b:Feet N D)(v:Geometry N →Z→Z)(f:Site (More N)→Z→Z→ℝ)(h:∀ i x y, 0≤f i x y) : Feet N (D × Z) where
 st:= { F := b.st.F
        home:=b.st.home
        drive:=fun i (x,y)=> (b.st.drive i x,v i y)
        eval:=fun S (x,y) (t,z)=> b.st.eval S x t + ∑ i∈S,f i y z
        pos:=fun S (x,y) (t,z)=> add_nonneg (b.st.pos S x t) (sum_nonneg (fun i _=> h i ..))
        includeV:=fun p x y=> add_le_add (b.st.includeV p x.1 y.1) (sum_le_sum_of_subset_of_nonneg p (fun i _ _=>h i x.2 y.2)) }
 town:=b.town
 index:=b.index
variable [TopologicalSpace D][TopologicalSpace D']
structure Skid (b:Feet N D)(c:Feet N D')(φ:D'→D) : Prop where
 cont : Continuous φ
 cov (g x) : φ (c.st.drive g x)= b.st.drive g (φ x)
 price (S x y) : b.st.eval S (φ x) (φ y)≤ c.st.eval S x y
namespace Skid
variable {b:Feet N D}{c:Feet N D'}{φ:D'→D}(h:Skid b c φ){p:Pay}{A:D→Op (Single N)}
def carries (k: Tag b.st) : Tag c.st where
 run:=k.run
 keeps (g i j) e := k.keeps g i j (by rw [b.index]; rwa [c.index] at e) -- h unused
include h
lemma earn {s t:Tag b.st}(H:Earn p s t A): Earn p (carries (c:=c) s) (carries (c:=c) t) (fun x=> A (φ x)):= H.restrict φ h.cont (b.town.trans c.town.symm) (b.index.trans c.index.symm) h.price id (fun _ _=>(h.cov ..).symm) rfl rfl
lemma mark (H: Earn p b.mark b.mark A): Earn p c.mark c.mark (fun x=> A (φ x)):= h.earn H -- defeq
end Skid
omit [TopologicalSpace D'] in
lemma doubleSkid [TopologicalSpace Z](b:Feet N D) (v:Geometry N→ Z→Z)(f:Site (More N)→Z→Z→ℝ)(h:∀ i x y,0≤f i x y): Skid b (b.double v f h) Prod.fst:= ⟨continuous_fst,fun _ _=>rfl,fun S x y=> le_add_of_nonneg_right (sum_nonneg fun i _=> h i x.2 y.2)⟩ -- tune omit
end Feet
abbrev HScope (N:Side)(r:ℝ):= {A:Quilt N//∀ i, ‖A i‖≤r}
namespace HScope
variable {r:ℝ}(b:Feet N D)
def move (g:Geometry N)(H: HScope N r): HScope N r:=⟨stitch g H.val,fun i=>(congr_norm ..).trans_le (H.property i)⟩
def hueD (i:Site (More N))(v w:HScope N r):ℝ:=‖v.val i-w.val i‖
def palette (r:ℝ) : Feet N (D× HScope N r):= b.double move hueD (fun i x y=> norm_nonneg (x.val i - y.val i))
variable [TopologicalSpace D]
lemma skid (r:ℝ) : b.Skid (palette b r) Prod.fst:= Feet.doubleSkid ..
lemma buys (h:1≤r): ∃ p:Pay, ∀ {D:Type}[TopologicalSpace D]{N:Side}(b:Feet N D), let t:=palette b r; Earn p t.mark t.mark.reverseV (fun x=> pair x.2.val):=by
 obtain ⟨p,S⟩:=earnsTile r h; refine ⟨p,?_⟩; intro D _ N b t; apply S (F:=fun i:D×HScope N r=> i.2.val) t (continuous_subtype_val.comp continuous_snd) (fun _ _=>rfl) (fun i x=> i.2.property x) ; intro x y i; let j:=badgeOf i; change hueD j _ _ ≤r*(b.st.eval {j} x.1 y.1 + ∑ l∈({j}:Seal _), hueD l x.2 y.2); rw [sum_singleton]; have ht := b.st.pos {j} x.1 y.1; have hp:0≤ hueD j x.2 y.2:= norm_nonneg _; exact le_trans (le_add_of_nonneg_left ht) (le_mul_of_one_le_left (add_nonneg ht hp) h)
end HScope
end YM.CF.BProof.Spin
