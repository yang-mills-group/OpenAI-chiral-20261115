import YM.CF.Rel.Bone
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
def atU(G:Gauge)(v:G.El)(x:InputZ G n):InputZ G n:= fun j=>G.adjoint v (x j)
def actU(G:Gauge)(v:G.El)(n:Side): InputZ G n→L[ℝ]InputZ G n:= LinearMap.toContinuousLinearMap { toFun:=atU G v, map_add':=fun x y=>funext fun i=>map_add _ _ _,map_smul':=fun x y=>funext fun i=>map_smul (G.adjoint v) x (y i) }
variable {f:SpaceX G n}{o:Site n}
lemma roll_o(h:Atom f o r)(he:ContDiffAt ℝ m (satX f) 0)(g:G.El)(J:Fin m→InputZ G n): cake m (satX f) J = cake m (satX f) (atU G g ∘ J):=by
 let L:=actU G g n; have hx:satX f=satX f ∘ L:=by
    ext1 p; change f _= f (represent _); rw [show represent (L p)=gauge (fun _=>g) (represent p) from ?_,h.fixed]
    ext1 i; unfold Lattice.gauge; simp_rw [Work.F03.represent_link]; exact Next.SectorChange.exp_adjoint ..
 unfold cake; simp only [_root_.smul_apply]; congr 1; conv_lhs=> rw [hx]
 rw [Push.Uniform.iter_lin_at (L:=L) ((map_zero L).symm ▸ he),map_zero]; rfl
private lemma punctual(f:G.El→Delph G m) (h:∀ x: Fin m→ G.Color,Continuous fun g=> f g x) : Continuous f:=by
 classical
 let I:=Fin m→Fin (Module.finrank ℝ G.Color); let b:= Module.finBasis ℝ G.Color
 let L:=LinearMap.pi (R:=ℝ) fun i:I=> (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m=>G.Color) ℂ (fun j=> b (i j))).toLinearMap
 have he: L.ker=⊥:=LinearMap.ker_eq_bot'.mpr (fun X hx=>by
    ext p; conv_lhs=> rhs; rw [show p=(fun i=> ∑ j,(b.repr (p i)) j • b j) from funext (fun i=>(b.sum_repr _).symm)]
    rw [ContinuousMultilinearMap.map_sum]; refine Finset.sum_eq_zero fun i _=>?_; rw [X.map_smul_univ (fun j:Fin m=> (b.repr (p j)) (i j))]; rw [show X (fun j=> b (i j))=0 from congr_fun hx i,smul_zero])
 obtain ⟨g,e⟩:= LinearMap.exists_leftInverse_of_injective L he
 have hp:f=g ∘ (L ∘ f):=by funext x; exact (DFunLike.congr_fun e (f x)).symm
 rw [hp]; exact g.continuous_of_finiteDimensional.comp (continuous_pi fun i=> h _)
def dock (P:Delph G m)(g:G.El):Delph G m:= P.compContinuousLinearMap fun _=> (G.adjoint g).toContinuousLinearMap
lemma ad_j(x: G.Color):Continuous fun i:G.El=> G.adjoint i x:=by simp only [Gauge.adjoint,LinearMap.coe_mk,AddHom.coe_mk, Gauge.conjugate]; apply G.projectColor.continuous_of_finiteDimensional.comp (f:=fun i=>_*_*_); fun_prop
lemma dock_u(P:Delph G m): Continuous (dock P):= punctual _ fun x=> P.contDiff (n:=ω) |>.continuous.comp (continuous_pi fun i=> ad_j (x i))
def rope (P:Delph G m):Delph G m:=∫ i,dock P i ∂G.probHaar
lemma rope_u(P:Delph G m)(x:Fin m→G.Color): rope P x=∫ i:G.El,P (fun j=>G.adjoint i (x j)) ∂G.probHaar:= ((ContinuousMultilinearMap.apply ℝ _ _ x).integral_comp_comm ((dock_u P).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
lemma rope_h(P:Delph G m): ‖rope P‖≤‖P‖:=by
 have ht(g:G.El): ‖dock P g‖≤ ‖P‖:=by apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; apply mul_le_of_le_one_right (norm_nonneg _); refine prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=> ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_); intro x; rw [one_mul]; exact (G.norm_adjoint g _).le
 apply (norm_integral_le_of_norm_le_const (μ:=G.probHaar) (ae_of_all _ ht)).trans_eq; simp
lemma Rope(P:Delph G m) (x:Fin m→G.Color)(g:G.El): rope P (fun i=> G.adjoint g (x i))=rope P x:=by rw [rope_u,rope_u]; simp_rw [← G.adjoint_mul]; exact integral_mul_right_eq_self (μ:=G.probHaar) (fun g=> P (fun i=> G.adjoint g (x i))) _
def Trade(P: Delph G m):Prop:=∀ x:Fin m→G.Color,∀ g:G.El,P (fun i=>G.adjoint g (x i))=P x
@[simp] lemma rope0: rope (0:Delph G m)=0:=by ext1; rw [rope_u]; simp
lemma sumH_p(u:InputZ G n)(z:Body 2 n)(g:G.El): G.adjoint g (sumH G u z)=sumH G (atU G g u) z:=by
 obtain ⟨⟨x,p⟩,rfl⟩:= (ŧ n).surjective z; change G.adjoint g (dColor _ _ _ u (x,plaquette p))= dColor G n 1 (atU G g u) (x,plaquette p)
 rw [← fundamental, ← fundamental]
 have he (o:Site n)(p:Walk): G.adjoint g (linkSum (collect G u) o p)=linkSum (collect G (atU G g u)) o p:=by
    induction p generalizing o with
    | nil=> rw [linkSum,linkSum,map_zero]
    | cons i _ ih=> cases i with| mk i b=> cases b <;> simp [linkSum,collect,atU,ih]
 exact he _ _
lemma oblige(h:Atom f o r)(hs:ContDiffAt ℝ m (satX f) 0)(hp:cFoot m (satX f))(hz:payG r<n.val)(hc:‖cake m (satX f)‖≤ C): ∃ W:KitM G n m,(∑ i,‖W i‖) ≤ payM m r*C∧(∀ i:Disk n m,Trade (W i)) ∧ (∀ i,i∉Pots o (payG r) m→ W i=0)∧ ∀ J:Fin m→InputZ G n, cake m (satX f) J=∑ p,engages W p J:=by
 obtain ⟨P,hP,hV,H⟩:=plaque h hs hp hz hc
 refine ⟨rope∘P,(sum_le_sum (g:=fun i=> ‖P i‖) fun _ _=> rope_h _).trans hP,fun i=> Rope (P i),fun i hv=>by rw [Function.comp_apply,hV i hv,rope0],fun J=>?_⟩
 simp_rw [engages,Function.comp_apply,rope_u]; rw [← integral_finsetSum]
 · have he(g:G.El): ∑ i:Disk n m,P i (fun j=>G.adjoint g (sumH G (J j) (i j)))= cake m (satX f) J:=by nth_rw 1 [roll_o h hs g]; rw [H]; simp_rw [sumH_p]; rfl
   simp [he]
 intro i _; exact ((P i).contDiff (n:=ω)|>.continuous.comp (continuous_pi fun j=> ad_j _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end YM.CF.Rel
