import YM.CF.Gall.Lamb
import YM.CF.Kea.Cool
import YM.CF.Flare.Coda
import GaugeFieldConstruction.WingGate
/-! # P3 similarity on exact momenta. Never set momentum 0 in cost receive phase. -/
set_option autoImplicit false
set_option maxHeartbeats 25000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Fock.Flux
open Function Filter Metric NormedSpace Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {j:ℕ} {r C:ℝ}
variable {N:Side}
abbrev boardC (N:Side)(j:ℕ)(M:Jill.Male):= spar j M (1: Bkg (More N)) -- tune expects Skin N? good
abbrev shoe (N:Side)(j:ℕ)(M:Jill.Male) (i:Stag N):Op SpinIdx:=field (too N) j M i
abbrev orbV (N:Side):= fun _:Stag N=> Aop
abbrev amplitude (i:Site N):= ‖pm i‖
lemma amplitude_pin (i:Site N): pinch N ≤ amplitude i:=by
 apply (cohere (N:=N) (i 0)).trans
 apply le_trans _ (norm_le_pi_norm (pm i) 0)
 exact le_rfl
lemma amplitude_pos (i:Site N): 0 < amplitude i:= (pinch_pos N).trans_le (amplitude_pin i)
lemma amplitude_top (e:Even N.val)(i:Site N): amplitude i≤Real.pi:=by
 have ht:= up_p (too N) e (i,Classical.arbitrary Slot); rw [too_u] at ht; exact ht
lemma shoe_P (e:Even N.val)(i:Stag N)(j:ℕ)(M:Jill.Male): IsStarProjection (shoe N j M i):= by
 let S:=too N; have ht:=firm_bar j M.val M.property (base_subset_realCube zone_pos (b_base (up_p S e i))); exact ⟨ht.1,ht.2⟩
lemma basic_band (e:Pad j N) (M:Jill.Male): boardC N j M=Dofu N (shoe N j M):=by
 have he:=e.2 emptyC (too N) M; have ht: tax emptyC = (1:Bkg (More N)):=by
    funext i; have hv : Matrix.diagonal (pw ∘ (emptyC i.2).val)=(1:Op SU.F):= by ext x y; by_cases e:x=y; subst y; simp [emptyC,skyV,phase_z]; simp only [Matrix.diagonal_apply_ne _ e,Matrix.one_apply_ne e]
    apply Subtype.ext; apply Subtype.ext; exact hv
 rw [ht] at he; exact he
lemma baseP (e:Pad j N)(M:Jill.Male): IsStarProjection (boardC N j M):= by rw [basic_band e]; exact idol (too N) j M e.1
abbrev slit (i:Site N)(j:ℕ)(M:Jill.Male):=disk j M (pm i)
lemma slit_positive (h:1≤j)(e: Even N.val)(i:Site N)(M:Jill.Male):0<slit i j M:=by
 obtain ⟨c,d,s,t,g⟩:= zip h; have hp:0<amplitude i:= amplitude_pos _; exact (mul_pos s (pow_pos hp 2)).trans_le ((g _ _ (show Bound Real.pi _ from amplitude_top e i)).1)
lemma shoe_choose (e:Even N.val)(i:Stag N)(j:ℕ)(M:Jill.Male): Aop*shoe N j M i*Aop=(slit i.1 j M) • Aop:= by rw [←Complex.coe_smul]; have he:=footQ (too N) e j M i; rw [too_u] at he; exact he
abbrev tilt_scar (i:Stag N)(j:ℕ)(M:Jill.Male):= scarH (shoe N j M i) Aop (slit i.1 j M)
abbrev pinShift (N:Side)(j:ℕ)(M:Jill.Male):= Dofu N (1+fun i=> tilt_scar i j M)
abbrev pinBack (N:Side)(j:ℕ)(M:Jill.Male):= Dofu N (1-(fun i=> tilt_scar i j M))
lemma token_V (e:Pad j N)(h:1≤j)(M:Jill.Male): Valve (boardC N j M) (tickA N) (pinShift N j M) (pinBack N j M):=by
 rw [basic_band e,landP]; 
 let A:= shoe N j M; let T:= Dofu N; let E:=orbV N
 let f(i:Stag N):=tilt_scar i j M; let X:=1+f; let Y:=1-f
 have h(i:Stag N): Valve (A i) Aop (X i) (Y i):= scar_forms (shoe_P e.1 i j M) A_id (slit i.1 j M) (slit_positive h e.1 i.1 M) (shoe_choose e.1 i j M)
 change Valve (T A) (T E) (T X) (T Y); refine ⟨?_,?_,?_,?_,?_⟩
 · rw [←map_mul,show X*Y=1 from funext fun i=>(h i).live,map_one]
 · rw [←map_mul,show Y*X=1 from funext fun i=>(h i).rest,map_one]
 · rw [←map_mul,show X*A=A from funext fun i=> (h i).carry]
 · rw [←map_mul,show Y*A=A from funext fun i=> (h i).bring]
 rw [←Dofu_s,←map_mul,←map_mul,←map_mul,show A*star Y*E=star Y*E from funext fun i=> (h i).home]
lemma board_rank (e:Pad j N) (M:Jill.Male): Matrix.trace (tickA N)= Matrix.trace (boardC N j M):=by rw [basic_band e]; exact meanV ..

abbrev bMove (N:Side)(j:ℕ)(M:Jill.Male)(b:ℝ):= chips (boardC N j M) b * pinShift N j M
abbrev bReturn (N:Side)(j:ℕ)(M:Jill.Male)(b:ℝ):= pinBack N j M*chips (boardC N j M) (-b)
abbrev stemMove (N:Side)(j:ℕ)(M:Jill.Male)(b:ℝ)(i:Stag N):= chips (shoe N j M i) b*(1+tilt_scar i j M)
abbrev stemRet (N:Side)(j:ℕ)(M:Jill.Male)(b:ℝ)(i:Stag N):= (1-tilt_scar i j M)*chips (shoe N j M i) (-b)
lemma chips_Do (e:Pad j N) (M:Jill.Male)(b:ℝ): Dofu N (fun i=> chips (shoe N j M i) b)= chips (boardC N j M) b:=by
 rw [basic_band e]; let F:= (shoe N j M); unfold chips; let X:= Real.exp (-b); let Y:= Real.exp b; change Dofu N (X • F+ Y • (1-F))=_; rw [map_add,map_smul,map_smul,map_sub,map_one]
lemma MoveV (e:Pad j N)(M:Jill.Male)(b:ℝ): bMove N j M b= Dofu N (stemMove N j M b):=by unfold bMove; rw [←chips_Do e, pinShift, ←map_mul]; rfl
lemma RetV (e:Pad j N)(M:Jill.Male)(b:ℝ): bReturn N j M b= Dofu N (stemRet N j M b):=by unfold bReturn; rw [←chips_Do e, pinBack, ←map_mul]; rfl
lemma floor_C (h:1≤j):∃ C:ℝ,0<C ∧ ∀ {N:Side},Even N.val→∀ (i:Stag N)(M:Jill.Male), ‖tilt_scar i j M‖ ≤ C/amplitude i.1 :=by
 obtain ⟨a,c,e,f,P⟩:=zip h; let A:=Real.sqrt a; have hp: 0<A:=Real.sqrt_pos.mpr e; refine ⟨A⁻¹, inv_pos.mpr hp,fun {N} E i M=>?_⟩; let T:= tilt_scar i j M; let W:=slit i.1 j M; have hv:=scar_norm (shoe_P E i j M) A_id (slit_positive h E i.1 M) (shoe_choose E i j M); let r:= amplitude i.1; have hg:a*r^2 ≤ W:= (P _ _ (show Bound _ _ from amplitude_top E _)).1; have he : A*r ≤ Real.sqrt W:= by rw [show A=Real.sqrt a from rfl, ←Real.sqrt_sq (show 0≤ r from norm_nonneg _),← Real.sqrt_mul e.le]; exact Real.sqrt_le_sqrt hg -- might rewrites W def?
 rw [le_div_iff₀ (amplitude_pos _)]; rw [inv_eq_one_div,le_div_iff₀ hp]; let k:=amplitude i.1; change ‖T‖* k*A ≤ 1; change Real.sqrt W*‖T‖ ≤1 at hv; change A*k ≤ _ at he; nlinarith only [hv,mul_le_mul_of_nonneg_left he (norm_nonneg T)]
lemma move_cost (b:ℝ)(h:1 ≤ j): ∃ C>0,∀ {N:Side}, Even N.val → ∀ (M:Jill.Male)(p:ℝ),|p|≤ b → ∀ i:Stag N,
 ‖stemMove N j M p i‖≤ C/amplitude i.1 ∧ ‖stemRet N j M p i‖≤ C/amplitude i.1:=by
 obtain ⟨A,s,g⟩:= floor_C h; let y:= 2*Real.exp b; have hy:0<y:=by unfold y; positivity
 refine ⟨y*(Real.pi+A),mul_pos hy (add_pos Real.pi_pos s),fun {N} E M p hp i=>?_⟩ -- N implicit tune
 have u:=amplitude_top E i.1; let r:=amplitude i.1; have hr:0<r:= amplitude_pos _; have he: 1+A/r ≤ (Real.pi+A)/r:=by rw [le_div_iff₀ hr,add_mul,one_mul,div_mul_cancel₀ _ hr.ne']; linarith only [u]
 let K:= (Real.pi+A)/r; let X:= tilt_scar i j M; have ht:‖X‖≤A/r:=g E i M; have hw:‖(1:Op SpinIdx)‖ ≤1:= (le_of_eq norm_one)
 have hh:=chips_budget p b hp (shoe_P E i j M); have hg:=chips_budget (-p) b (by simpa) (shoe_P E i j M)
 rw [mul_div_assoc]; exact ⟨(norm_mul_le ..).trans (mul_le_mul hh ((norm_add_le ..).trans ((add_le_add hw ht).trans he)) (norm_nonneg _) hy.le), (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left hg (norm_nonneg _)).trans ((mul_le_mul_of_nonneg_right ((norm_sub_le ..).trans ((add_le_add hw ht).trans he)) hy.le).trans_eq (mul_comm K y)))⟩
end YM.CF.Fock.Flux
end
