import YM.CF.Urn.Combo
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {N P:Side}{L:Side}(G:Ratio N P)(e:ℝ)
abbrev Co : Type:= Coil N P × Chin P
def cro :Set (Co (N:=N) (P:=P)):= (legal G e) ×ˢ Openc (More P) e
def hall(e:ℝ): Stage (Site (More P)) (Iota G) ↥(cro G e) (Site (More P)→ E) where
 F:= (tempo G e).F
 drive h x:=let V:Openc (More P) e:=⟨x.val.2,x.property.2⟩; ⟨(jazz G h x.val.1,((forum P e).drive h V).val),surface G h e x.property.1, ((forum P e).drive h V).property ⟩
 home:= (tempo G e).home
 eval S x y:= deal G S x.val.1 y.val.1/|e|+ fare S x.val.2 y.val.2/|e|
 pos S x y:= add_nonneg (div_nonneg (deal_pos ..) (abs_nonneg _)) (div_nonneg (fare_t ..) (abs_nonneg _))
 includeV S x y:= add_le_add (div_le_div_of_nonneg_right (deal_le G S ..) (abs_nonneg _)) (div_le_div_of_nonneg_right (fare_inc S ..) (abs_nonneg _)) -- parameter
abbrev pinH(v:Bool):Tag (hall G e):= ⟨(parcel G v e).run,(parcel G v e).keeps⟩
variable {e} {b x y a r:ℝ}{u v: Bool}{m:ℕ}
def walkH (t:cro G e): ↑(legal G e):= ⟨t.val.1,t.property.1⟩
def aidH(t:cro G e): ↑(Openc (More P) e):=⟨t.val.2,t.property.2⟩
lemma room_S (H: legal G e→ Op (Iota G))(C:Toll (Iota G))(S: Seal (Site (More P)))(p:Suite (badge _) (parcel G u e) (parcel G v e) S C H) : Suite (badge _) (pinH G e u) (pinH G e v) S C (H ∘ walkH G):=by
 refine ⟨⟨fun g t=>p.frame g (walkH _ t),fun i j=>?_ ⟩,fun i j X h q u=>p.fuel i j X h (walkH _ ∘ q) u.fst⟩; have he:= p.expo i j
 exact ⟨he.positive,he.triggered,fun x=>he.bounded _,fun x y=> (he.variation _ _).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (show 0 ≤ fare S x.val.2 y.val.2/|e| from div_nonneg (fare_t ..) (abs_nonneg _))) he.positive),he.connected.comp ((continuous_fst.comp continuous_subtype_val).subtype_mk _) ⟩
lemma room_L (H:Raw (legal G e) (Iota G))(h:Street (badge _) (parcel G u e) (parcel G v e) m x a (fun _=> b) H): Street (badge _) (pinH G e u) (pinH G e v) m x a (fun _=>b) (H ∘ walkH G):=by obtain ⟨F,C,p,k,g⟩:=h; exact ⟨_,C,fun i=>room_S G _ _ _ (p i),k,fun x=>g _⟩ -- tune
lemma room_c (H:Raw (legal G e) (Iota G))(h:Crown (badge _) (parcel G u e) (parcel G v e) a b H):Crown (badge _) (pinH G e u) (pinH G e v) a b (H ∘ walkH G):=by obtain ⟨F,C,p,k,g⟩:=h; exact ⟨_,C,fun i=>room_S G _ _ _ (p i),k,fun x=>g _⟩
lemma rideC(H:Raw (Openc (More P) e) (Single P))(h:Crown (badge _) (bail P e) (bail P e) a b H):Crown (badge _) (pinH G e true) (pinH G e true) a b (foot G ∘ H ∘ aidH G):=by
 let J:=switchG G; obtain ⟨F,C,K,q,l⟩:=h
 let C' S(i j: Iota G):= C S (J i) (J j); let F'(S: Seal (Site (More P)))(x: cro G e):= foot G (F S (aidH G x))
 have hh i j:saleM a C' i j=saleM a C (J i) (J j):=rfl
 refine ⟨F',C',fun S=>⟨⟨fun t x=>?_,fun i j=>?_ ⟩,fun i j V hV γ k=>?_ ⟩,⟨q.posP,fun i=>?_,fun i=>?_ ⟩,fun x=>?_ ⟩
 · change foot G (F S _) *foot G (tradew P _).val=foot G (tradew P _).val*foot G _; rw [←foot_mul,←foot_mul]; exact congr_arg _ ((K S).frame _ (aidH G x))
 · have hl:=(K S).expo (J i) (J j); exact ⟨hl.positive,hl.triggered,fun x=>hl.bounded _,fun x y=> (hl.variation (aidH G x) (aidH G y)).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show 0 ≤ deal G S x.val.1 y.val.1 / |e| from div_nonneg (deal_pos ..) (abs_nonneg _))) hl.positive), hl.connected.comp ((continuous_snd.comp continuous_subtype_val).subtype_mk _)⟩
 · exact (K S).fuel (J i) (J j) V hV (aidH G ∘ γ) k.snd
 · simp_rw [hh]; rw [Equiv.sum_comp]; exact q.rows _
 · simp_rw [hh]; apply le_trans (le_of_eq (Equiv.sum_comp J (fun x=> saleM a C x (J i)))) (q.cols _)
 change foot G (H (aidH G x))=_; rw [show H _= _ from l (aidH G x)]; ext; simp [F',foot,Matrix.sum_apply]
end YM.CF.Urn
