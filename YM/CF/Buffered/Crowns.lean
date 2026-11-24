import YM.CF.Graph.Sage
/-! Quantitative path comparison on the unmodified threshold. LOCAL for base
 terms on flags-empty. Atom services budget productions (ignore mismatches).
 Distances in chord units; elliptical rows may have unbounded lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Crust
open Function Filter Finset Lattice Wilson RG PathData Work.F03
open scoped InnerProductSpace Matrix.Norms.Frobenius BigOperators Topology Classical -- check no instance exported
variable {G:Gauge}{N P : Side}{F: PathData G} {c: Clip} {p: BudgetPoint} {v a u C L β:ℝ}
-- generic gauge avoids trouble with norms
variable (G)
def Dg (x y:G.El) := G.chord (x⁻¹ * y)
lemma Dg_comm (x y:G.El) : Dg G x y=Dg G y x:=by unfold Dg; rw [←G.chord_inv (x⁻¹*y),mul_inv_rev,inv_inv]; -- tune
lemma Dg_tri (x y z:G.El) : Dg G x z ≤ Dg G x y+Dg G y z:=by unfold Dg; apply le_trans _ (G.chord_triangle (x⁻¹*y) (y⁻¹*z)); rw [mul_assoc,←mul_assoc y _,mul_inv_cancel,one_mul]
lemma Dg_mul (a b x y:G.El):Dg G (a*b) (x*y)≤ Dg G a x+Dg G b y:=by
 have he:=Dg_tri G (a*b) (x*b) (x*y); refine he.trans_eq (congrArg₂ (fun a b:ℝ=>a+b) ?_ ?_); all_goals unfold Dg; rw [mul_inv_rev]
 · rw [show b⁻¹*a⁻¹*(x*b)= b⁻¹*(a⁻¹*x)*(b⁻¹)⁻¹ from by group,G.chord_conj]
 rw [mul_assoc, ←mul_assoc x⁻¹, inv_mul_cancel, one_mul]
lemma Dg_self (x:G.El):Dg G x x=0:=by simp [Dg]
lemma Dg_inv (x y:G.El) : Dg G x⁻¹ y⁻¹=Dg G x y:=by rw [Dg_comm G x]; unfold Dg; rw [inv_inv,show x*y⁻¹=x*(y⁻¹*x)*x⁻¹ from by group,G.chord_conj]
lemma Dg_lip (x y:G.El): |G.chord x-G.chord y|≤ Dg G x y:=by
 have h (x:G.El): Dg G 1 x=G.chord x:=by simp [Dg]
 apply abs_le.mpr; rw [←h x,←h y]; constructor <;> linarith [Dg_tri G 1 x y,Dg_tri G 1 y x,Dg_comm G x y]
private lemma Dg_frob (x y:G.El):Dg G x y=‖G.mat x-G.mat y‖/G.colorScale:=by
 unfold Dg Gauge.chord; congr 1; rw [G.mat_mul, show (1:G.Mat)= G.mat x⁻¹*G.mat x from by rw [← G.mat_mul, inv_mul_cancel,G.mat_one], ←mul_sub, Gauge.mul_frob_eq _ _ (G.mat_star_mul _), norm_sub_rev] -- tune name
lemma Dg_curve (x y:G.El): ‖G.curvature x-G.curvature y‖ ≤ Dg G x y:=by
 have hl : ‖G.mat x⁻¹-G.mat y⁻¹‖= ‖G.mat x-G.mat y‖:= (div_left_inj' G.colorScale_pos.ne'|>.mp (by rw [← Dg_frob,←Dg_frob,Dg_inv])) -- tune
 unfold Gauge.curvature; rw [←map_sub,←smul_sub, show G.mat x - G.mat x⁻¹-_=G.mat x-G.mat y-(G.mat x⁻¹-G.mat y⁻¹) from (by abel)]; rw [Dg_frob]
 refine le_trans (G.project_norm _) ?_; apply div_le_div_of_nonneg_right _ G.colorScale_pos.le; rw [norm_smul]; have ht:= norm_sub_le (G.mat x-G.mat y) (G.mat x⁻¹-G.mat y⁻¹); rw [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]; linarith
variable {G}
def Legend (s:ℕ) (v:ℝ) (U: Config G N)(W:Config G P)(x:Site N)(y:Site P) := ∀ l:Walk,l.length≤2*s → Dg G (travel U x l) (travel W y l) ≤ l.length*v
variable {U:Config G N}{W:Config G P}{x:Site N}{y:Site P}{s:ℕ}
private def ferry (x:RG.Slot) := x.walk ++ square x.plaq.val.1 x.plaq.val.2 ++ reverse x.walk
private lemma ferry_at (a:RG.Slot)(x:Site N)(U:Config G N): a.atSite U x=G.curvature (travel U x (ferry a)):=by
 rw [atSite_path, ← G.curvature_conjugate]; unfold ferry; rw [travel_append,travel_append,stop_append,square_stop,travel_reverse]; congr 3 -- tune
 change Lattice.travel _ (wrap N (stop 0 a.walk)+x) _= _; rw [wrap_stop_cover,map_zero, add_comm _ x, ← Work.E03.stop_add_left,add_zero]; rfl
lemma Legend.ellDept (p:F.Bounds c a C L) (w:Legend s v U W x y)(t:0≤v)(r:PlaqAxes) : ‖F.ell U (x,r)- F.ell W (y,r)‖≤ C*(2*s*v+4*Real.exp (-(a*s))) := by
 obtain ⟨A,h,H⟩:= p.rows r; let ℓ(k:ℕ):= (F.row r k).2; let c(k:ℕ):=|(F.row r k).1| *Real.exp (a*(ℓ k).length); let M:=2*s*v+4*Real.exp (-(a*s)); have hM:0≤M:=by unfold M; positivity
 have hx(k:ℕ): ‖F.ellTerms (x,r) k U-F.ellTerms (y,r) k W‖≤c k*M:=by
    let Q:=ℓ k; change ‖(F.row r k).1 • Q.atSite U x- (F.row r k).1 • Q.atSite W y‖≤_
    rw [←smul_sub,norm_smul]; unfold c; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have ht:= p.width; by_cases z: Q.length ≤ s
    · rw [ferry_at, ferry_at]; apply (Dg_curve ..).trans; have hu:(ferry Q).length ≤ 2*s:=by unfold ferry; simp [square,Lattice.reverse]; unfold RG.Slot.length at z; omega
      apply (w _ hu).trans; apply le_trans (mul_le_mul_of_nonneg_right (show ((ferry Q).length:ℝ) ≤ 2*s from by exact_mod_cast hu) t); apply le_trans (le_add_of_nonneg_right (by positivity : 0≤ 4*Real.exp (-(a*s)))); exact le_mul_of_one_le_left hM (Real.one_le_exp (by positivity))
    have hg : Real.exp 0 ≤ Real.exp (a*(Q.length:ℝ)-(a*s)):=Real.exp_le_exp.mpr (sub_nonneg.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast (lt_of_not_ge z).le) ht.le)) -- tune
    rw [Real.exp_zero, sub_eq_add_neg,Real.exp_add] at hg
    apply (norm_sub_le ..).trans; refine (add_le_add (Slot.eval_norm ..) (Slot.eval_norm ..)).trans ?_; unfold M
    have hn : 0 ≤ Real.exp (a*(Q.length:ℝ))*(2*s*v):=by positivity
    change (2:ℝ)+2 ≤ Real.exp (a*Q.length)*_; linarith
 unfold ell; rw [← Summable.tsum_sub]; rotate_left; · exact (F.ell_dominated p _).summable _ -- name
 · exact (F.ell_dominated p _).summable _
 have hv:Summable (fun k=>‖F.ellTerms (x,r) k U-F.ellTerms (y,r) k W‖):= Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hx (h.mul_right M); exact (norm_tsum_le_tsum_norm hv).trans ((hv.tsum_mono (h.mul_right M) hx).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right H hM))
lemma flags_calm (U:Config G N) (v:ℝ) : flags v U=∅↔∀ i:Face (Per N), G.chord (faceValue U i) ≤ v := by
 constructor
 · intro h i; by_contra! l; exact Finset.notMem_empty _ (α:=Site N) (h ▸ (flags_spec ..).2 ⟨i,Work.E01.base_touched _,l⟩)
 intro h; apply eq_empty_iff_forall_notMem.mpr; intro i h'; obtain ⟨i',_,t⟩:= (flags_spec ..).1 h'; linarith [h i']
lemma simple (h:flags p.threshold U=∅) (i:Face (Per N)) : F.baseTerm c p U i=c.direct*G.chord (faceValue U i)^2/2 + ‖F.ell U i‖^2/2:=by
 have he:= (flags_calm U p.threshold).1 h
 unfold baseTerm clipped; rw [if_pos (he i),if_pos (show kept c p.threshold i.1 U from fun q=> (he q).trans (le_mul_of_one_le_right p.threshold_pos.le (Real.one_le_exp (by have h:= c.radius_pos; positivity))))]
def bend_cost (s:ℕ)(v a C d:ℝ):= d*(8*v)+2*C*(C*(2*s*v+4*Real.exp (-(a*s))))
lemma Legend.toll (h:F.Bounds c a C L)(v':Legend s v U W x y)(ha:2 ≤ s)(u:0≤v)(k:flags p.threshold U=∅)(l:flags p.threshold W=∅) (g:0≤ C)(i:PlaqAxes) : F.baseTerm c p U (x,i)-F.baseTerm c p W (y,i)≤ bend_cost s v a C c.direct:=by
 let D:= G.chord (faceValue U (x,i)); let D':= G.chord (faceValue W (y,i)); have hd: D-D' ≤ 4*v:=(le_abs_self _).trans ((Dg_lip ..).trans ((v' (square i.val.1 i.val.2) (by unfold square; simp; omega)).trans_eq (by simp [square])))
 have hD: (D-D')*(D+D') ≤ 4*v*4:= mul_le_mul hd (by linarith only [show D≤2 from G.chord_le_two _, show D'≤2 from G.chord_le_two _]) (by unfold D D'; exact add_nonneg (G.chord_nonneg _) (G.chord_nonneg _)) (by positivity)
 rw [simple k,simple l,add_sub_add_comm]; let B:=2*s*v+4*Real.exp (-(a*s)); let A:= ‖F.ell U (x,i)‖; let A':=‖F.ell W (y,i)‖
 have hu: A-A' ≤ C*B:= (norm_sub_norm_le ..).trans (v'.ellDept h u i)
 have hw: A+A' ≤ C*2+C*2:= add_le_add (Graph.pea h U (fun _=>G.chord_le_two _) (by norm_num) _) (Graph.pea h W (fun _=>G.chord_le_two _) (by norm_num) _)
 have hb:0 ≤ B:=by unfold B; positivity
 refine add_le_add ?_ ?_
 · change c.direct*D^2/2-c.direct*D'^2/2 ≤_; nlinarith only [mul_le_mul_of_nonneg_right hD c.quadratic_pos.le]
 change A^2/2-A'^2/2 ≤ 2*C*(C*B); nlinarith only [mul_le_mul hu hw (show 0≤ A+A' from add_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg g hb)]
end YM.CF.Buffered.Crust
#print axioms YM.CF.Buffered.Crust.Legend.toll
