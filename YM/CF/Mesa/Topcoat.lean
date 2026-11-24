import YM.CF.Mesa.Lieu

/-! Borel filling choices at a single cell. Healthy cell test at boundary stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {m B:Side} {a b c: Index m} {K L:ℝ}
abbrev Au (m B:Side):=Bkg (Domain m B)
def Facebed (a:Index m)(K:ℝ)(U: Au m B)(v:Fa m B):=∀ b:Index m,Lesser b a→Bed b K U v
def well (a:Index m)(U:Au m B)(K:ℝ):=∃ v:Fa m B, Bed a K U v
lemma closed_bet (a:Index m)(K:ℝ) : IsClosed {x:Au m B×Fa m B| Bed a K x.1 x.2}:=by
  simp_rw [show ∀x:Au m B × Fa m B, Bed a K x.1 x.2↔∀ e:Edge _, Plug a e→ GDist (x.2 e.1*x.1 e) (x.2 (e.1+step e.2)) ≤ K/B.val from fun _=> Iff.rfl,setOf_forall]; apply isClosed_iInter; intro e; apply isClosed_iInter; intro p
  exact isClosed_le (Continuous.dist (SU.group.continuous_mat.comp (by fun_prop)) (SU.group.continuous_mat.comp (by fun_prop))) continuous_const
lemma well_closed (a:Index m)(K:ℝ) : IsClosed {x:Au m B | well a x K}:=by
  rw [show {x:Au m B|well a x K}= Prod.fst '' {x:Au m B×Fa m B|Bed a K x.1 x.2} by ext; simp [well]]; exact (((closed_bet ..).isCompact).image continuous_fst).isClosed
lemma well_local {U W:Au m B}(h:Agrees (room m B a) U W)(k:well a U K):well a W K:=by
  obtain ⟨v,hv⟩:= k; exact ⟨v,room_bed_le hv le_rfl h (fun _ _=>rfl)⟩
lemma pclosed (a:Index m)(K:ℝ)(v:Fa m B):IsClosed {x:Au m B|Facebed a K x v}:=by
  simp_rw [Facebed,setOf_forall]; apply isClosed_iInter; intro b; apply isClosed_iInter; intro h; simp_rw [←setOf_forall]; exact (closed_bet b K).preimage (continuous_id.prodMk (continuous_const (y:=v)))
lemma cloce {U:Au m B}{v w:Fa m B} {r:ℝ}(hp:∀ x, GDist (w x) (v x)≤ r) (h: Facebed a K U v):Facebed a (K+2*r*B.val) U w:=by
  rintro b ht ⟨x,i⟩ he; have hs:= dist_triangle4_right (SU.group.mat (w x*U (x,i))) (SU.group.mat (w (x+step i))) (SU.group.mat (v x*U (x,i))) (SU.group.mat (v (x+step i)))
  rw [bolt] at hs
  apply hs.trans
  apply (add_le_add (add_le_add (hp x) (hp _)) (h b ht _ he)).trans
  apply le_of_eq; have hz:0<(B.val:ℝ):=by positivity
  field_simp; ring
lemma kit_face (a:Index m)(r:ℝ)(hp:0<r)(L:ℝ): ∃ X:Finset (Fa m B),∀ U:Au m B,(∃ v,Facebed a L U v)→∃ v∈X,Facebed a (L+2*r*B.val) U v:=by
  classical
  let S (v:Fa m B): Site (Domain m B)→SU.group.Mat:=SU.group.mat ∘ v
  have ht:Continuous S:=continuous_pi fun i=>SU.group.continuous_mat.comp (continuous_apply _)
  obtain ⟨Y,g,h,Yx⟩:= finite_cover_balls_of_compact (isCompact_range ht) hp
  choose v p using fun i:Y=>g i.property
  letI:= h.fintype; refine ⟨Finset.univ.image v,?_⟩; rintro U ⟨u,q⟩
  obtain ⟨z,hZ,t⟩:=mem_iUnion₂.mp (Yx (mem_range_self u))
  let x:Y:=⟨z,hZ⟩; refine ⟨v x,Finset.mem_image_of_mem v (Finset.mem_univ x), cloce (fun i=>?_) q⟩
  change dist (S u) z < r at t; calc
    _ ≤ dist (S (v x)) (S u):= dist_le_pi_dist _ _ _
    _ ≤ _ := by rw [p,dist_comm]; exact t.le
lemma face_book {v:Fa m B}{U W:Au m B}(h:Agrees (room m B a) U W)(t:Facebed a K U v) :Facebed a K W v:= fun b g e w=>by -- missing variable
  have he:=plug_le g.1 w; rw [← h e he.1 he.2]; exact t b g _ w
lemma fixB (a:Index m)(K:ℝ):∃ Y:Au m B→Fa m B,Measurable Y∧(∀ U:Au m B,(∃ f,Facebed a K U f)→ Facebed a (K+2) U (Y U))∧ ∀ x y,Agrees (room m B a) x y → Y x=Y y:=by
  classical
  obtain ⟨F,H⟩:= kit_face (B:=B) a (1/(B.val:ℝ)) (by positivity) K
  have hB : K+2*(1/(B.val:ℝ))*B.val=K+2:=by
    have ht : 0<(B.val:ℝ):=by positivity
    field_simp
  rw [hB] at H
  have he (F:Finset (Fa m B)):∃ Y:Au m B→Fa m B,Measurable Y∧(∀ U:Au m B,(∃ v∈F,Facebed a (K+2) U v)→Facebed a (K+2) U (Y U))∧ ∀ x y,Agrees (room m B a) x y → Y x=Y y:=by
    induction F using Finset.induction_on with
    | empty=> refine ⟨fun _=>1,measurable_const,fun U v=>by simpa using v,fun _ _ _=> rfl⟩
    | insert i S ht ih =>
      obtain ⟨Y,l,e,h⟩:= ih; refine ⟨({x|Facebed a (K+2) x i}:Set (Au m B)).piecewise (fun _=>i) Y, Measurable.piecewise ((pclosed ..).measurableSet) measurable_const l,fun U u=>?_,fun U X y=>?_⟩
      · by_cases g:Facebed a (K+2) U i
        · rw [piecewise_eq_of_mem _ _ _ g]; exact g
        rw [piecewise_eq_of_notMem _ _ _ g]; apply e; obtain ⟨v,w,p⟩:=u
        exact ⟨v,(Finset.mem_insert.mp w).resolve_left (fun r=>g (r ▸ p)),p⟩
      have he:Facebed a (K+2) U i ↔ Facebed a (K+2) X i:=⟨fun g=>face_book y g,fun g=>face_book (fun p u v=>(y p u v).symm) g⟩; simp [piecewise, he, h U X y]
  obtain ⟨Y,p,h,v⟩:=he F; exact ⟨Y,p,fun U t=> h U (H U t),v⟩
end YM.CF.Mesa
