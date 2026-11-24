import YM.SU5.FiniteGaugeData.Brique.Trio
import YM.SU5.FiniteGaugeData.Brique.Twig
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Spire Tenant Fock Fock.Brique Tulip Dial Fir Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N L B:Side} {σ : Window.Family} {S:Finset (Site N)} {R T U : Support (More N)} {t:List (Site N)} {k n j:ℕ} {a b c e f r:ℝ}
local notation "Μ" => Single N
-- linear span of ONLY nonempty syntax lists, and even each has only one at each seed, plus site in S, all lower in R. Have a row-wise center covariance test per LIST; buying sums afterwards. 
inductive Barque (σ:Window.Family)(S: Finset (Site N))(R: Support (More N)): FC (Single N) → Prop
| stage {A:FC (Single N)} (t:List (Site N)) (nonidle:t≠[]) (unique:t.Nodup) : t.toFinset⊆S→ Trio σ N R t A → Barque σ S R A
| zero : Barque σ S R 0
| add {A B:FC (Single N)}: Barque σ S R A → Barque σ S R B → Barque σ S R (A+B)
| mul {A:FC (Single N)} (c:ℂ): Barque σ S R A → Barque σ S R (c • A)
variable {X:Op (Single N)}{Y:FC (Single N)}
lemma Barque.mono (P:Barque σ S R Y){S':Finset (Site N)} (h:S⊆S'): Barque σ S' R Y:=by
 induction P with| stage i g u v w=> exact .stage i g u (v.trans h) w| zero=> exact .zero| add _ _ a b=> exact .add a b | mul c _ d=>exact .mul c d
lemma Barque.fines (P:Barque σ S R Y)(h:S.image node⊆T)(v:R⊆T): Reed.Fine (Tset N) (modesIn N T) false Y:=by
 induction P with| stage t _ _ z l=> exact l.fines (fun i g=> h (mem_image_of_mem _ (z (List.mem_toFinset.mpr g)))) v| zero=> exact .empty _| add _ _ a b=> exact a.add b| mul _ _ h=> exact h.scale _
lemma Barque.wind (P:Barque σ S R Y)(x:Seat N→SU.E): Barque σ S R (flipsP x Y):=by induction P with | stage i f g u w=> exact .stage i f g u (w.wind x)| zero=> rw [map_zero]; exact .zero | add _ _ a b=> rw [map_add]; exact .add a b| mul _ _ h=> rw [flipsP,twist_scalar]; exact .mul _ h
lemma Barque.agrow (P:Barque σ S R Y)(i:Site N) (q:i∉S)(x y:Ket (Single N))(hx:withinM (capU σ i) x)(hy:withinM (lumen σ R) y) : Barque σ (insert i S) R (Y*(create x* Fock.remove y)):=by
 induction P with
 | stage t v g h w => exact .stage (i::t) (by simp) (List.nodup_cons.mpr ⟨fun m=>q (h (List.mem_toFinset.mpr m)),g⟩) (by rw [List.toFinset_cons]; exact insert_subset_insert _ h) (w.action i x y hx hy)
 | zero => rw [zero_mul]; exact .zero
 | add _ _ a b => rw [add_mul]; exact .add a b
 | mul _ _ h=> rw [Algebra.smul_mul_assoc]; exact .mul _ h
-- Gauge and Family determinism on our matrix-level preaveraging certificates. Before field projections. 
structure Etude (σ:Window.Family)(S:Finset (Site N))(T:Support (More N))(P:Op (Single N))(a b:ℝ)(X:FC (Single N)) :Prop where
 rays : Barque σ S (T\ S.image node) (X-1)
 weight : ‖X‖ ≤ (1+b)^ S.card
 prime : ∃ A:Op (Single N),Cellar (modesIn N T) A ∧ IsStarProjection A ∧ A.trace= S.card ∧ TapFn false A (acts (star X) (mateK N)) ∧ ‖A*P‖≤a
section
-- heads
variable (S T σ)
private theorem chooseG (σ:Window.Family): ∃ x∈ (colors σ),True:=by
 have he:0<(colors σ).card:=by rw [colors_card]; unfold dimf; split <;> decide
 obtain ⟨i,p⟩:= card_pos.mp he; exact ⟨i,p,trivial⟩ -- tune
local notation "Q" => cutM (atSites S)
def knob (x:Site N)(σ:Window.Family):Single N:=((x,0),Classical.choose (chooseG σ))
lemma knob_p (x:Site N): knob x σ ∈ capU σ x:=mem_inter.mpr ⟨(grade_one _ _).mpr (by decide),mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(Classical.choose_spec (chooseG σ)).1⟩, (sites_eq ..).mpr (mem_singleton_self _)⟩⟩
private lemma knobS : Injective (fun x:Site N=> knob x σ):=fun _ _ t=> congrArg (fun x:Single N=> x.1.1) t
def seedlings (S:Finset (Site N))(σ:Window.Family): Finset (Single N):=S.image (fun x=> knob x σ)
local notation "μ" => seedlings S σ
lemma knob_h : μ ⊆ atSites S:=by intro i t; obtain ⟨i,v,rfl⟩:= mem_image.mp t; exact (sites_eq ..).mpr v
lemma knob_g : μ ⊆ Tset N:=by intro i t; obtain ⟨i,-,rfl⟩:= mem_image.mp t; exact (mem_inter.mp (knob_p σ i)).1
lemma knob_u(i:Single N)(t:i∈ μ): family i.2=σ:=by obtain ⟨i,-,rfl⟩:= mem_image.mp t; exact (is_cap ..).1 (knob_p σ i)|>.2.1
lemma knob_size(N:Side)(S:Finset (Site N)): (seedlings S σ).card= S.card:= card_image_of_injective S (knobS σ)
lemma knob_injective : Set.InjOn (fun i:Single N => i.1.1) (μ:Set (Single N)):=by
 intro i a j b q; obtain ⟨i,u,rfl⟩:=mem_image.mp a; obtain ⟨j,v,rfl⟩:=mem_image.mp b; exact congrArg (fun i=> knob i σ) q
lemma hat_cut (A B:Finset (Single N)): Commute (cutM A) (cutM B) := by unfold Commute SemiconjBy; rw [cut_meet,cut_meet,inter_comm]
private lemma hcColor (M:Male)(hk:1 ≤ k): Commute (cutM (classOf σ N)) (funde k M N 1):=by
 unfold Commute SemiconjBy ; ext i j; rw [funde_flat k hk,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; simp only [Matrix.kroneckerMap_apply,in_class]
 by_cases h:i.2=j.2; · rw [h]; simp [mul_comm]
 rw [Matrix.one_apply_ne h]; simp
variable (X)
local notation "A" => SampleOp S X T
local notation "P₀" => cutM μ
private lemma colorLaw(X:Op (Single N))(f:Commute (cutM (classOf σ N)) X) (t:IsUnit (1-implant S X)):Commute (cutM (classOf σ N)) (SampleOp S X T):= by
 exact Commute.mul_right (Commute.mul_right (Commute.mul_right (Commute.mul_right (hat_cut ..) ((Commute.one_right _).sub_right f)) (hat_cut ..)) (unit_com ((Commute.one_right _).sub_right (((hat_cut ..).mul_right f).mul_right (hat_cut ..))) t)) (hat_cut ..)
private lemma sample_ways (p:Q*A=Q)(u:cutM (modesIn N T)* A=A)(v: Commute (cutM (classOf σ N)) A)(i:Single N)(h:i∈ seedlings S σ): withinM (lumen σ (T\S.image node)) (acts (cutM (Tset N)ᶜ*A) (basisKet i)):= by
 apply (within_test ..).mpr; intro k hk; rw [act_mul,cut_apply]; by_cases g:k∈(Tset N)ᶜ; swap; · rw [if_neg g]
 rw [if_pos g]; let W:= acts A (basisKet i); change W.ofLp k=0; by_cases e:k∈ classOf σ N; swap
 · have hz:withinM (classOf σ N) W:= by unfold withinM W; rw [←act_mul,v.eq,act_mul,cut_basis,if_pos ((in_class ..).2 (knob_u σ S i h))]
   exact (within_test ..).mp hz _ e
 have hv: withinM (modesIn N T) W:=by unfold withinM W; rw [←act_mul,u]
 by_cases l:k∈ modesIn N T; swap; · exact (within_test ..).mp hv _ l
 have he:k∈ atSites S:=shroom S ▸ (modes_at ..).mpr (show node k.1.1∈S.image node from (by by_contra w; apply hk ((is_lumen ..).mpr ⟨mem_compl.mp g,(in_class ..).1 e, mem_sdiff.mpr ⟨(modes_at ..).1 l,w⟩⟩))) -- syntax
 have hW:acts (cutM (atSites S)) W = basisKet i:=by unfold W; rw [←act_mul,p,cut_basis,if_pos (knob_h σ S h)]
 have hi:k≠ i:=fun v=>absurd (knob_g σ S h) (v ▸ mem_compl.mp g)
 have hx:=congrArg (fun w:Ket (Single N)=>w.ofLp k) hW; simp only [cut_apply,if_pos he,basis_apply,if_neg hi] at hx; exact hx
lemma lift_bar (R:Support (More N))(X:Op (Single N))(h:∀ i∈μ,withinM (lumen σ R) (acts (cutM (Tset N)ᶜ*X) (basisKet i))): Barque σ S R (star (starMark0 (Tset N) X μ)-1):= by
 let f(V:Finset (Single N)):= star (starMark0 (Tset N) X V); let Lift(V:Finset (Single N)):Finset (Site N):=V.image fun i=> i.1.1
 have ht(V:Finset (Single N))(z: V⊆ μ):Barque σ (Lift V) R (f V -1):=by
    induction V using induction_on_min with
    | empty=> rw [show f ∅=1 from (by simp [f,starMark0,column]) ,sub_self]; exact .zero
    | insert i V k ih=>
       let U:=insert i V; let y:=i.1.1; let A':= starBoost (Tset N) X i; let t:V⊆μ:= (subset_insert i V).trans z; let I:i∈μ:=z (mem_insert_self i V); let c:=acts (cutM (Tset N)ᶜ*X) (basisKet i); let E:= Lift V; let H:= (create (basisKet i)* remove c); have hk:i∉ V:=fun e=>lt_irrefl _ (k i e)
       have hp:(star A')=1+H:=by unfold A'; rw [starBoost_star, show H=_ from congrArg (fun z=> z*_) (create_put i)] -- tune
       have hu:f (insert i V)=f V*star A':=by unfold f; rw [starMark0,column,sort_insert _ (fun j hj=> (k j hj).le) hk,List.map_cons,List.prod_cons,star_mul]; rfl
       have he:= within_basis (capU σ y) i ((is_cap _ _).mpr ⟨knob_g σ S I,knob_u _ _ _ I,rfl⟩); have hv:y∉Lift V:=by intro f; obtain ⟨i',u,r⟩:=mem_image.mp f; exact hk ((knob_injective σ S (t u) I r) ▸ u) -- tune
       let Y:=ih t; let Q':= Trio.action y _ c he (h i I) (Trio.unit (σ:=σ) (N:=N) (R:=R));
       rw [hu,hp,show Lift (insert i V)=insert y (Lift V) from image_insert ..,show f V*(1+H)-1=(f V-1)+((f V-1)*H+1*H) from (by noncomm_ring)]
       exact .add (Y.mono (subset_insert ..)) (.add (Y.agrow _ hv _ _ he (h i I)) (.stage [y] (by simp) (by simp) (by simp) Q'))
 apply (ht μ le_rfl).mono; intro i f; obtain ⟨v,p,rfl⟩:=mem_image.mp f; exact (sites_eq ..).mp (knob_h σ S p)
-- actually root stage fee 
lemma prepared_trick (hk:1≤k)(M:Male)(X':X=funde k M N 1)(p: IsStarProjection X)(u: Lattice.halo j (S.image node) ⊆ T)(t:‖implant S X‖ ≤ 1-e)(l:0<e)(o:∃ Y, Neighbor j Y ∧ ‖Y-X‖ ≤ b):∃ F: FC (Single N), Etude σ S T X (b*e⁻¹) e⁻¹ F:=by
 have ht:= Subset.trans (halo_subset ..) u; let L:=(implant_early _ S t l); let E:= A; let Q₁:=cutM (seedlings S σ); let F:=starMark0 (Tset N) E μ
 have he:(cutM (atSites S))*A=cutM _:= pins_value _ _ L _ ht; have hy:= lift_bar σ S (T\S.image node) A (sample_ways σ S T X he (sample_region ..) (colorLaw _ _ _ _ (X' ▸ hcColor σ M hk) L)) -- order
 refine ⟨star F,hy,?_,?_⟩
 · rw [norm_star,←knob_size σ N S]; exact starM_cost (Tset N) μ E (inv_pos.mpr l).le (sample_size S X L _ t l p)
 let Y:= E*Q₁; have hx:Y*Q₁=Y:=by unfold Y; rw [mul_assoc,show Q₁*Q₁=Q₁ from (cutM_idp _).1];
 have hz:Q₁*Y=Q₁:=by unfold Y; let X:=cutM (atSites S); have hp:Q₁*X=Q₁:= (cut_meet ..).trans (congrArg cutM (inter_eq_left.mpr (knob_h ..))); rw [←mul_assoc]; nth_rw 1 [←hp]; rw [mul_assoc Q₁ X E, (show X*E=X from he),hp,(show Q₁*Q₁=Q₁ from (cutM_idp _).1)] -- order binding semicolon
 let W:= Fock.Brique.Ortho Y; have hw:IsStarProjection W:= ortho_project Y
 refine ⟨W, ortho_cellar _ (by unfold Y; rw [←mul_assoc,(show cutM _*E=E from sample_region ..)]),hw,?_,?_,?_⟩
 · rw [tankL_trace _ _ hx hz,trace_cut,knob_size]
 · rw [star_star]; exact starM_complete (Tset N) μ E (knob_g ..) ((mul_assoc _ _ _).trans hz) _ (touchP _ ▸ tickB _)
 rw [←norm_star,star_mul,p.2.star_eq,hw.2.star_eq]; nth_rw 1 [show W=Y*W from (tankL_quad Y Q₁ hx hz).symm]
 rw [←mul_assoc]; refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (hw.norm_le _)).trans ?_); unfold Y; rw [←mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans (sample_spill _ _ L _ u t l p o))
end
end YM.CF.Window.Brique
