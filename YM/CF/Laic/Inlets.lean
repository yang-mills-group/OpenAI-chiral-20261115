import YM.CF.Laic.Rug
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {c f L:Side}(G:Ratio c f){a b d:ℝ}{k:ℕ}
lemma emptio (x y: Site c): separation (G.embed x) (G.embed y) = G.count.val*separation x y:=by
 unfold separation; rw [← Ratio.root_embed,← Ratio.root_embed, ←map_sub, Ratio.root_embed]; let v:= x-y; let i:Finset Axis:=univ; unfold pdist; simp_rw [Ratio.lift_embed,Pi.smul_apply,nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]; -- sup
 let f:=fun i=> (lift (x-y) i).natAbs; apply le_antisymm; · exact Finset.sup_le fun i hi=> Nat.mul_le_mul_left _ (Finset.le_sup (f:=f) hi)
 obtain ⟨i,hp,h⟩:= Finset.exists_mem_eq_sup _ univ_nonempty f; refine le_trans ?_ (Finset.le_sup (f:=fun i=> G.count.val*f i) hp); exact Nat.mul_le_mul_left _ h.le
lemma highest (i:Iota G)(p:en G i)(h:Odd G.count.val):lookM G i=(ratio G).embed (place_x (modest G i)):= pledge G i p 1 h
lemma trK (i:Single c)(ho:Odd G.count.val): lookM G (patchQ G i)=(ratio G).embed (place_x i):=by change lookM G (rideG G i)=_; rw [highest G _ (en_ride ..) ho]; rfl
variable {T:RG.StepData (More c) (More f)}(F:Forest T.ratio)(h:T.ratio=ratio G)(v:G.count=L)
def popH (T:RG.StepData (More c) (More f)) :Single c→Site (More f):= T.ratio.embed ∘ place_x
include h v
lemma yon_F: ∀ i:Signed,Yoke (clothH T F) (Yg (incX i) ∘ fine SU.group F) (id ∘ (incX i).anon f) (2*L.val):=by
 intro i; apply lagY i
 refine ⟨fun i j=>?_,fun {u v} i he=>?_⟩; change separation i j≤ L.val * _; nth_rw 1 [←one_mul (separation i j)]; exact Nat.mul_le_mul_right _ L.property
 apply fine_read F he i; simp only [h,Rush.ratio,id_eq,separation_self,zero_add]; rw [‹G.count=L›]
lemma yon_O :∀ i:Signed,Yoke (clothH T F) (Yg (incX i) ∘ outer SU.group F) (T.ratio.embed ∘ (incX i).anon c) (2*L.val):=by
 intro i; apply lagY i; refine ⟨fun i j=>?_,fun i e=> co_read F e i ?_⟩; rw [emptio,h]; change G.count.val*_≤_; rw [v]
 simp
omit h v F
lemma frame_y {ι:Type}[Fintype ι]{l:ι→ Site (More f)}{x:Positions ι}{D:Positions ι→Op (Single f)}(p: CableM l place_x place_x a k D x b): CableM l (lookM G) (lookM G) a k (fun y=>foot G (D y)) x b:=fun r i j => p r (switchG G i) (switchG G j)
lemma order_y {ι:Type}[Fintype ι]{l:ι→Site (More f)}{x:Positions ι}{D:Positions ι→Op (Single c)}(ho:Odd G.count.val)(h:0<a)(t:0≤b)(p:CableM l ((ratio G).embed∘place_x) ((ratio G).embed∘ place_x) a k D x b): CableM l (lookM G) (lookM G) a k (fun y=>endorse G (D y)) x b:=by
 intro r i j; unfold coinZ endorse extendK; by_cases hx:en G i ∧ en G j
 · rw [highest G i hx.1 ho, highest G j hx.2 ho]; simp only [Function.comp_apply, Matrix.map_apply,Matrix.of_apply,if_pos hx]; exact p r (modest G i) (modest G j)
 simp only [Function.comp_apply,Matrix.map_apply,Matrix.of_apply, hx,ite_false,map_zero,thread_none,mul_one]; apply ((allows_const (n:=k) x (le_refl ‖(0:ℝ)‖)).beacon (r:=0) (s:=Set.univ) (fun _ _ _ _ _=>rfl) univ_mem h.le).mono; simp; exact mul_nonneg t (decay_pos ..|>.le)
lemma signV {ι:Type}[Fintype ι]{l:ι→Site (More f)}{x:Positions ι}{D:Positions ι→Op (Iota G)}(ho:Odd G.count.val)(p:CableM l (lookM G) (lookM G) a k D x b):CableM l ((ratio G).embed ∘ place_x) ((ratio G).embed ∘ place_x) a k (fun y=>summit (patchQ G) (D y)) x b:=by
 intro r i j; have hx:= p r (patchQ G i) (patchQ G j); rw [trK G i ho, trK G j ho] at hx; exact hx
-- sky multiplicity
lemma ringM {Y:Type}[Fintype Y](v:Y→Single f)(p:Injective v): Multiplicity (place_x∘ v) (Fintype.card (SpinIdx × Slot)) :=by
 apply Multiplicity.comp ?_ p; intro z; let Z(i:Single f):SpinIdx × Slot:= (i.1.2,i.2)
 let F:=univ.filter (fun i=>place_x i=z)
 have he:Set.InjOn Z (↑F):=by
    rintro ⟨⟨i,w⟩,s⟩ h ⟨⟨j,u⟩,t⟩ r ht; let T:=assembly f; have hv:= Prod.mk.inj (show (w,s)=(u,t) from ht); have hx:= (mem_filter.mp (show _∈ F from h)).2.trans ((mem_filter.mp (show _∈ F from r)).2).symm; have hr:i=j:= T.embed_injective (add_right_cancel (show T.embed i+1=T.embed j+1 from hx)); rw [hr,hv.1,hv.2] -- type 1
 exact (Finset.card_le_card_of_injOn Z (t:=Finset.univ) (fun i _=> Finset.mem_univ _) he).trans_eq (card_univ)
lemma tally: Multiplicity (lookM G) (Fintype.card (SpinIdx × Slot)):=ringM _ (switchG G).injective
end YM.CF.Laic
