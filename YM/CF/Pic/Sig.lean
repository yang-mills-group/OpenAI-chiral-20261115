import YM.CF.Pic.Loft
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b:ℝ}{P:Grasp Y B e}
lemma profile_m :∃ C:ℝ,1≤C ∧∀ N:Side,∀ U V:Bkg N,∀ k:ℝ,0≤k→lawnK U V k→‖profile U-profile V‖≤C*k:=by
 obtain ⟨C,c,H⟩:=gulf; refine ⟨C,c,fun n u v k t p=>?_⟩; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; have he:‖brand (u i)-brand (v i)‖≤C*k:= by rw [Prod.norm_def]; exact max_le ((H _ _).trans (mul_le_mul_of_nonneg_left (p i) (by positivity))) ((p i).trans (le_mul_of_one_le_left t c))
 apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro b; cases b; exact (by change ‖star (brand (u i))-star (brand (v i))‖≤_; rw [←star_sub,norm_star]; exact he); exact he
lemma marchC (p:1≤j):∃ A a:ℝ,0<A ∧0<a∧∃ v:ℕ,∀ N:Side,v≤N.val →∀ V W:Bkg (More N),Guard V a→Guard W a→∀ M:Jill.Male,∀ k:ℝ,0≤k→lawnK V W k→‖spar j M V-spar j M W‖≤ A*k:=by
 obtain ⟨a,r,e,h,hc,l,v,Q⟩:= funde_s _ p; obtain ⟨C,k,L⟩:=profile_m; refine ⟨r*(4/a)/e*C,e,by positivity,l,v,fun n g u W hx hg M s b z=>?_⟩
 refine (landscape (Q M n g) h l (profile u) (profile W) (⟨u,hx,by simpa⟩) ⟨W,hg,by simpa⟩).trans ?_; exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (L _ _ _ _ b z) l.le) (by positivity : 0≤r*(4/a))).trans_eq (by ring)
abbrev poleC(N:Side):Op (Single N):= postC (vacuumW N)
lemma spoke(j:ℕ)(p:1≤j)(M:Jill.Male)(N:Side):spar j M (1:Bkg (More N))*poleC N=poleC N* cc (spar j M (1:Bkg (More N))):=by
 let G:= idrat N; let F:= foal j true M G (vacancyY N N).1; have hp:F=foot G (spar j M (1:Bkg _)):=rfl -- profile? still_u
 have hz: helmC G=foot G (poleC N):=by rw [← helm_eq G true,vacancyY]; exact square_true G _
 have he:= homeT G j M true p; rw [hz,show foal j true M G _= _ from hp,cc_foot,←foot_mul,←foot_mul] at he; ext i k; obtain ⟨i,rfl⟩:= (switchG G).surjective i; obtain ⟨k,rfl⟩:= (switchG G).surjective k; exact Matrix.ext_iff.mpr he i k
lemma lease_x {v:ℝ}(e:v<b)(U:Bkg (More N))(h:lawnK U 1 v):Slow U (hook (vacuumW N)) b:=by
 intro x i; let V:Vect:=Dial.apex.val; change ‖turn (U (x,i)) V - V‖<_
 have he:V= turn (1:E) V:=by unfold Lat.turn; rw [fund_one, act_one]
 refine lt_of_le_of_lt (le_trans ?_ ((h (x,i)))) e; calc
    ‖turn _ V-V‖ = ‖turn (U (x,i)) V-Lat.turn 1 V‖:=by rw [←he]
    _ ≤ _:=turn_price _ _ V
    _ = _:=by rw [show ‖V‖=1 from bib _,mul_one]; rfl
-- cost diff hum
lemma debt0{E D G:Type}[Fintype E][DecidableEq E][TopologicalSpace D](p:Light E D G)(X:Draw D)(a C:ℝ)(f:D→ℂ)(h:Screen p X 1 f a C)(hp:0≤a)(s:Set ℝ)(q:IsOpen s)(u:ℝ→ D)(t:X.test ℝ s u){x:ℝ}(v:x∈s): Allows 1 (f ∘ u) x (Fintype.card E*C):=by
 obtain ⟨U,P,H,g,G'⟩:=h
 have hx:= allows_sum (f:=fun i:Seal E=>U i ∘ u) (C:=P) (fun i (_:i∈univ)=> (H i).plot _ _ q _ t x v)
 rw [show f ∘ u= _ from funext fun i=> G' (u i)]; apply hx.mono
 unfold hitE hit0 at g; calc
    _ ≤ ∑ j:Seal E, ∑ i∈ j,P j :=sum_le_sum fun i _=>by
      by_cases h:P i=0; rw [h]; simp
      have t:i.Nonempty:=by cases (H i).travel h <;> simp
      exact single_le_sum (fun _ _=> (H i).pos) t.choose_spec
    _ ≤ _:=by
      have he (i:Seal E): (∑ j∈i,P i)=∑ j:E,if j∈i then P i else 0:= by rw [←Finset.sum_filter]; simp
      simp_rw [he]; rw [sum_comm]; refine (sum_le_sum (g:=fun _=>C) fun i _=>?_).trans_eq (by simp)
      apply le_trans _ (g i); rw [sum_filter]; apply sum_le_sum; intro j _; split_ifs; apply le_mul_of_one_le_left (H _).pos; unfold Branch.rent; exact Real.one_le_exp (by positivity); rfl
end YM.CF.Pic
