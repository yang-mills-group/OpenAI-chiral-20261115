import YM.SU5.FiniteGaugeData.Brique.Screw
import YM.CF.Cour.Culm
/-! Corona local-operator estimate. Input `Guard` only to Working height, never global good-plaquettes priced in the state. All estimates not depending on torus volume. Supplies both clocks. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Spire Tenant Buffered Fock Fock.Brique Tulip Dial Skye Scree Cascade Nacre Paige Vault Branch
open Cour
attribute [local instance] opCStarAlgebra
variable {m L B : Side}{j k n:ℕ}{o:Odd L.val}{Y: Pricing k L o (Thread k)}
variable {c C e d r v:ℝ}
local notation "μ"=> fun t:Support (More m)=> cutM (modesIn m t)
open Fir
section
variable {F:Chin m→Op (Single m)}(h: Solo c C F e)(w:ℕ)
variable (G: Seal (Seat m) → Raw ↥(Openc (More m) e) (Single m)) (A:Seal (Seat m) → Branch.Toll (Single m))(p:∀ S,Ticket (bail m e) (bail m e) S (A S) (G S))(J: Branch.Ledger c A C)(leaves:∀ x: Openc (More m) e,F x.val=∑ S,G S x)(he:0<e)(g:0≤c)(x y:Openc (More m) e)
include G A p J leaves he g
abbrev tailCost (c C:ℝ)(w:ℕ):= Real.exp (-c/2*w)*C
lemma catalog_lop (x):‖F (x:Openc (More m) e).val-Branch.lop G w x‖ ≤ tailCost c C w:=by
 let Q:= tailCost c C w; let S:= RootedK (bail m e) (bail m e)
 have hx: S (c/2) Q (fun y=>(F y.val)-Branch.lop G w y):= lip_tail G A p J (v:=w) (F:=fun x=>F x.val) leaves g
 exact RootedK.boundOp hx (show 0≤ c/2 by linarith) x
omit he J leaves g in
lemma catalog_neighbor : Neighbor w (Branch.lop G w x):=neighbor_entry (Branch.lop_rad G A p x)
-- Fare scaled in LICENSE; buys POV every Guardian. Use norm in EVERY row-col.
lemma lop_short_variation (S U: Support (More m))(k: Lattice.halo w S ⊆ U) (ht: Tulip.fare U x.val y.val ≤ e*r): ‖(μ S)*(Branch.lop G w x-Branch.lop G w y)‖ ≤ r*C := by
 have h'U : (forum m e).eval U x y ≤ r := (by change Tulip.fare _ _ _ / |e|≤_; rw [abs_of_pos he]; apply (div_le_iff₀ he).mpr; exact ht.trans_eq (mul_comm ..))
 have hr:0≤r:=(show 0≤ (forum m e).eval U x y from (forum m e).pos ..).trans h'U
 let T:= (fun S i j=>r*A S i j); have h0(s i j):0≤T s i j:= mul_nonneg hr ((p s).nonn i j); have t:=sale_nn h0 c; have hJ:=J.funds hr; apply Branch.schur (saleM c T) _ _ hJ.posP _ hJ.rows hJ.cols
 intro i j; let D:= Branch.lop G w; let u:= ch (Seat m) w; let E i':= G i' x-G i' y; dsimp only; rw [cutM,Matrix.diagonal_mul]; by_cases f:i∈modesIn _ S; swap; · rw [if_neg f,zero_mul,norm_zero]; exact t i j
 rw [if_pos f,one_mul,Branch.lop,Branch.lop,Matrix.sub_apply,Matrix.sum_apply,Matrix.sum_apply, ←sum_sub_distrib]; apply (norm_sum_le ..).trans; refine le_trans (sum_le_sum (g:=fun s=> rent c s*T s i j) ?_) (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun s _ _=>mul_nonneg (rent_pos ..).le (h0 ..)))
 intro s a; apply (le_mul_of_one_le_left (h0 ..) (rent_one g s)).trans'; let W:=A s i j; refine le_trans (((p s).expo i j).variation x y) ?_
 by_cases q:W=0; · change W * _ ≤ r*W; rw [q,zero_mul,mul_zero]
 obtain ⟨G',F,H⟩:= ((p s).expo i j).triggered q
 let e' : s⊆U:=by intro j v; exact k (halo_spec.mpr ⟨node i.1.1,(modes_at ..).mp f,((show _ from G'.lim _ F j v).trans (mem_filter.mp a).2).le⟩)
 have hx: Tulip.fare s x.val y.val / |e| ≤ r:=le_trans (div_le_div_of_nonneg_right (Tulip.fare_inc e' x.val y.val) (abs_nonneg _)) h'U
 exact le_trans (mul_le_mul_of_nonneg_left hx ((p s).nonn i j)) (mul_comm W r).le -- tune
lemma local_length (S U:Support (More m))(k:Lattice.halo w S⊆ U)(ht:Tulip.fare U x.val y.val ≤ e*r) : ‖(μ S)*(F x.val-F y.val)‖ ≤ 2*tailCost c C w + r*C:=by
 have hez (x:Openc (More m) e):‖(μ S)*(F x.val-Branch.lop G w x)‖ ≤ tailCost c C w:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _)).trans (catalog_lop w G A p J leaves he g x)) -- order
 let f:=Branch.lop G w; have hv : F x.val-F y.val= (F x.val-f x)-(F y.val-f y) + (f x-f y):=by abel
 rw [hv,mul_add,mul_sub (μ S) (F x.val-f x)]; apply (norm_add_le ..).trans; refine add_le_add ?_ (lop_short_variation w G A p J leaves he g x y _ _ k ht); exact (norm_sub_le ..).trans ((add_le_add (hez x) (hez y)).trans_eq (two_mul _).symm) -- tune lt
end
-- operator tools on any ambient
structure Casing (n:Side)(e:ℝ)(F:Pane n→ Op (Single n)) (c C δ:ℝ) : Prop where
 delay_R : 0<δ
 paid : e ≤ δ
 prep : 0≤ c
 organic : ∃ K: Chin n→ Op (Single n),Solo c C K δ ∧ ∀ U:Pane n, F U=K (profile U) -- tune b unused! remove
variable {F:Pane m→Op (Single m)}
variable (H:Casing m e F c C d)
include H
lemma ambient_value (W:Pane m)(u:Guard W e): ‖F W‖ ≤ C:=by
 obtain ⟨h,k,t,p,z,v⟩:= H
 rw [v]; exact z.lib.boundOp t ⟨profile W,W,u.shrink k,by simpa⟩
lemma shape_fee (w:ℕ) (X Y:Pane m)(p:Guard X e)(q:Guard Y e)(S U: Support (More m))(s:Lattice.halo w S ⊆ U)(P:Tulip.fare U (profile X) (profile Y) ≤ d*r): ‖(μ S)*(F X-F Y)‖ ≤ 2*tailCost c C w+r*C:=by
 obtain ⟨h,k,t,F,z,v⟩:= H; let x:Openc (More m) d:= ⟨profile X,X,p.shrink k,by simpa⟩; let y:Openc (More m) d:= ⟨profile Y,Y,q.shrink k,by simpa⟩; obtain ⟨G,A,H,J,L⟩:= z.lib; rw [v,v]; exact local_length w G A H J (F:=F) L h t x y S U s P
lemma casing_neighbor (w:ℕ)(X:Pane m)(u:Guard X e) : ∃ A, Neighbor w A ∧ ‖A-F X‖ ≤ tailCost c C w:=by
 obtain ⟨h,k,t,F,z,v⟩:= H; let x:Openc (More m) d:= ⟨profile X,X,u.shrink k,by simpa⟩; obtain ⟨G,A,H,J,L⟩:= z.lib; refine ⟨_,catalog_neighbor w G A H x,?_⟩; rw [v,norm_sub_rev]; exact catalog_lop w G A H J (F:=F) L h t x
omit H
structure Terrace (k:ℕ)(u v a b:ℝ)
    (w:ℕ)(c C e:ℝ): Prop where
 l:e>0
 level:c>0
 value:C>0
 sparks : ∀ {m:Side},w ≤ m.val → ∀ M:Male,∀ d≤e, Casing m d (spar k M) c C e
 tanker : ∀ {m:Side}(T:Interest m),w ≤ m.val → T.P.toll u v a b → ∀ d ≤ e, Casing m d (blend k T false) c C e
lemma terrace (u v a b:ℝ)(p:0<u)(q:0<v)(ha:0≤a)(hb:0≤b)(hk:1≤k):∃ (w:ℕ)(c C e:ℝ), Terrace k u v a b w c C e := by
 let X:=arcB u v a b; let G:WG (QuotaH u v a b):=fun i=>funde k i.2
 let Y:WG (QuotaH u v a b):=fun i N x=>G i N x+(1-G i N x)*X i N x*G i N x
 have he:Lively G:= Urn.boost _ (funde_s k hk) Prod.snd; have hx : Lively Y:= he.add ((((Lively.one.sub he).prod (alum ha hb p q).1).prod he))
 obtain ⟨c,C,e,hp,hq,h,n,T,H⟩:= he.link hx
 refine ⟨n,c,C,e,⟨h,hp,hq,?_ , ?_⟩⟩; swap
 · intro m J ht f d l; obtain ⟨i,j,z⟩:= demand m ha hb J.P f J.M; refine ⟨h,l,hp.le,Y i m,H i m ht,fun k=> ?_⟩; unfold Y G X arcB; rw [j,z,Moire.bloom_P]; rfl -- let hygiene
 intro m t M d w; obtain ⟨i,-,z⟩:=demand m ha hb _ (xx0 (s:=v) (r:=u) m ha hb) M; exact ⟨h,w,hp.le,G i m,T i m t,fun p=>z ▸ rfl⟩ -- tune
lemma tailCloud (c C:ℝ)(h:0<c): Tendsto (fun w:ℕ=>tailCost c C w) atTop (𝓝 0):=by
 apply Tendsto.congr' ?_ (show Tendsto (fun w:ℕ=>Real.exp ((-c/2)*(w:ℝ))*C) atTop _ from ?_) -- maybe simp
 · exact Eventually.of_forall fun i=> rfl
 simpa using Tendsto.mul_const C (Real.tendsto_exp_atBot.comp (show Tendsto (fun w:ℕ=> -c/2*w) atTop atBot from tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith))) -- order
end YM.CF.Window.Brique
