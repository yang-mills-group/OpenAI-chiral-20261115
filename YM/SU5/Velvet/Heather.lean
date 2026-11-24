import YM.SU5.Velvet.Stamen
import YM.SU5.FiniteGaugeData.Pannier.Exacts
/-!
 # Upper berth for all actual δ-guarded panes
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 240000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Velvet
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side} {j n w d:ℕ} {z u v η ζ δ:ℝ}
namespace Hours
lemma Tfree (g:Seat N→ SU.E): twist (tradew N g) (tickA _) = tickA _:=by rw [touchP]; exact gauge_frostT g
lemma priceBack {n:Type*}[Fintype n][LinearOrder n][Nonempty n](U:UNI n)(B:Op n)(g:IsUnit B):twist U B⁻¹=(twist U B)⁻¹:=by
 apply Eq.symm; apply Matrix.inv_eq_right_inv; rw [←map_mul,(live g).1,map_one]
lemma hinge_cov {P:Pane N}{M:Tulip.Male} (Q:Sparkle N δ M j)(p:Guard P δ) (g:Seat N→ SU.E)(z): twist (tradew N g) (hinge (spar j M P) (tickA N) z)= hinge (spar j M (Lattice.gauge g P)) (tickA N) z:=by unfold hinge gate; simp only [map_add,map_smul,map_one,map_sub,map_mul,Q.covary _ g p, Tfree]
lemma account_cov {P:Pane N}{M:Tulip.Male} (Q:Sparkle N δ M j)(p:Guard P δ) (g:Seat N→ SU.E)(c:0<z)(ℓ:z≤1):
 draft (spar j M (Lattice.gauge g P)) (tickA N) z= twist (tradew N g) (draft (spar j M P) (tickA _) z):=by
 unfold draft panel; rw [map_mul,map_mul, priceBack _ _ (hinge_unit (Q.projection P p) (Kea.cut_t _) c ℓ), hinge_cov Q p]; simp only [gate,map_mul,map_add,map_smul,map_sub,map_one,Q.covary P g p,Tfree] -- rewriting loops direction? covary lhs
lemma track_cov {P:Pane N}{M:Tulip.Male} (Q:Procurement j n δ)(H:n≤N.val)(p:Guard P δ) (g:Seat N→ SU.E)(c:0<z)(ℓ:z≤1)(r:Rails):
 nectar j z r N M (Lattice.gauge g P) = twist (tradew N g) (nectar j z r N M P):=by
 let A:= Difference j z r N M; let f:= located j z r N M; let V:=Lattice.gauge g P; let X:= twist (tradew N g)
 have ht:X (A P)= A V:=by unfold A Difference; simp only [Pi.one_apply,Pi.sub_apply]; rw [map_sub, map_one]; exact congrArg (fun W:Op (Single N)=> W-(1:Op _)) (hinge_cov (Q.audit H) p g z) -- type
 have hv:IsUnit (f P):=nearOne ((lightening Q c ℓ r N P H p M).trans_lt (sub_lt_self 1 (pow_pos c _)))
 have hX : f V = X (f P):=by unfold f X located; rw [Fock.beam,Fock.beam,map_add,twist_scalar, map_one]; change 1+(r.val:ℂ) • A V = _; change 1+(r.val:ℂ) • A V=1+(r.val:ℂ) • X (A P); rw [ht]
 let Y(q:Pane N):= Real.log z • (tickA N - spar j M q) + (1/2:ℝ) • ((f q)⁻¹ * A q)
 change Y V=X (Y P); have hΤ:X (f P)⁻¹=(f V)⁻¹:=by rw [hX]; exact priceBack (tradew N g) (f P) hv
 have hg:X (spar j M P)=spar j M V:= ((Q.audit H).covary P g p).symm; have hx₀:X (tickA N)= tickA N:= Tfree ..
 unfold Y; rw [map_add,map_smul,map_smul,map_sub,map_mul,ht,hΤ,hg,hx₀]
-- cost per seat
abbrev modeX (i:Single N):= node i.1.1
def pet (x:Seat N):Finset (Single N):= univ.filter fun i=> modeX i=x
def spotQ (x:Seat N) (A:Op (Single N)):= (A*Vo {x}).trace
lemma spot_reveals (x:Seat N)(A:Op (Single N)):spotQ x A=∑ i∈pet x,A i i:=by
 unfold spotQ Matrix.trace Vo cutM; rw [pet,sum_filter]; apply sum_congr rfl; intro i _; unfold Matrix.diag; simp only [Matrix.mul_diagonal, modes_at,mem_singleton]; unfold modeX; split <;> simp [*]
lemma spot_cost (x:Seat N): (pet x).card ≤ 180 :=by
 let T (i:Single N): SpinIdx×SU.Slot:=(i.1.2,i.2); have ht: Fintype.card (SpinIdx×SU.Slot)=180:=by rw [Fintype.card_prod,slots,show Fintype.card SpinIdx=4 by simp [SpinIdx]]
 rw [← Finset.card_image_of_injOn (s:=pet x) (f:=T) ?_]; exact (card_le_univ _).trans_eq ht
 rintro ⟨⟨i,a⟩,t⟩ p ⟨⟨k,b⟩,u⟩ q h; rw [show i=k from needle ((mem_filter.mp p).2.trans (mem_filter.mp q).2.symm),show a=b from congrArg Prod.fst h, show t=u from congrArg Prod.snd h]
lemma spot_bound (x:Seat N)(A:Op (Single N))(p:‖A*Vo {x}‖≤u) :‖spotQ x A‖≤ 180 * u:=by
 have hv: spotQ x A=spotQ x (A*Vo {x}):=by unfold spotQ; rw [mul_assoc, (cutM_idp _).isIdempotentElem]
 rw [hv,spot_reveals]; apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun _=>u) (fun i _=> (norm_entry _ i i).trans p)).trans ?_; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast spot_cost x) ((norm_nonneg _).trans p)
lemma spot_cov (x:Seat N)(A:Op (Single N))(g:Seat N→SU.E):spotQ x (twist (tradew N g) A)=spotQ x A:=by unfold spotQ; nth_rw 1 [←gauge_frost {x} g]; rw [←map_mul,trace_twist]
lemma spot_total (N:Side)(A:Op (Single N)): ∑ x:Seat N,spotQ x A=A.trace := by
 simp_rw [spot_reveals]; exact sum_fiberwise _ modeX (fun i=>A i i)
lemma spot_sub (x:Seat N)(A B:Op (Single N)) : spotQ x (A-B)=spotQ x A-spotQ x B:=by rw [spotQ,sub_mul,Matrix.trace_sub]; rfl
open Py.Rate Py.Rate.Pannier RG
-- pointwise estimate, eventually U.r flagC . Convert to F.flags. P may differ. first only
lemma time_flowers (p:Procurement j n δ)(c:0<z)(q:z≤1)(e:ℝ)(w:0<e) : ∃ (B:ℕ)(v κ:ℝ), 0<v ∧ 0≤κ ∧ ∀ (b:ℝ),0≤b → b≤v→ ∀ (N:Side),B ≤ N.val→∀ (P: Pane N)(M:Tulip.Male), Guard P δ →
 trade (spar j M P) (tickA N) z ≤ trade (spar j M (1:Pane N)) (tickA N) z + e * sites N +κ* ((flags b P).card:ℝ) :=by
 let K:= nectar j z; let h:=worth p c q; obtain ⟨C,hC,H⟩:=h.price; obtain ⟨a,f,g,v⟩:=h.clean (e/180) (by positivity); obtain ⟨τ,τ0,t⟩:= stampG_price g a f; let d:=g+1; let s:ℕ:=(d+d+1)^4; let m:ℝ:= 180*(C+C); let k:= s*m;
 have hm:0≤ m:=by unfold m; positivity
 refine ⟨n+2*(g+1)+1,τ,k,τ0,by unfold k; positivity,fun b B u N n0 P M hp=>?_⟩
 let T:= Lattice.halo d (flags b P); have ht:n≤N.val:=by omega
 have hN:2*(g+1)<(More N).val:=by change _< N.val*2; omega
 let D:= (flags b P).card; have hD: T.card≤ D*s:=Corona.halo_size ..
 have hu(r:Rails)(x:Seat N) : ‖spotQ x (K r N M P - K r N M 1)‖ ≤ e+(if x∈T then m else 0):=by
    let q(A):= K r N M A; by_cases y:x ∈ T; · rw [if_pos y]; exact (spot_bound x (q P-q 1) ((voR _ _).trans ((norm_sub_le ..).trans (add_le_add (H r N P ht hp M) (H r N 1 ht (guard0 p.insp) M))))).trans (le_add_of_nonneg_left w.le)
    let V:= stampG x P; let A:= Lattice.gauge V P; have ha:Guard A δ:= hp.cov V
    have hz: Disjoint (BlockP d x) (flags b P):= disjoint_left.mpr fun i h g=> y (halo_spec.mpr ⟨i,g,(separation_comm ..).trans_le (blocks_test.mp h)⟩)
    have hh:= t b B u hN le_rfl x P hz; have hu: Rightful (BlockP g x) A 1 a:=hh
    have hκ: q A=twist (tradew N V) (q P):=track_cov p ht hp V c (by assumption) r
    rw [if_neg y,add_zero]; change ‖spotQ x (q P-q 1)‖ ≤e; rw [spot_sub,← spot_cov x (q P) V,← hκ,← spot_sub]; exact (spot_bound x (q A-q 1) ((v r N M A ht ha).2 _ hu)).trans_eq (by ring)
 have hI(r:Rails) : ‖(K r N M P-K r N M 1).trace‖≤ e* sites N+k*D:=by
   rw [← spot_total]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun x=> e+(if x∈ T then m else 0)) (fun x _=> hu r x)).trans ?_)
   rw [sum_add_distrib,sum_ite,sum_const_zero,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul,add_zero,filter_mem_eq_inter,univ_inter,card_univ]; rw [show Fintype.card (Seat N)=_ from site_card (More N)]; unfold sites k; refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ) |>.mpr hD) hm) _) (Eq.le ?_); push_cast; ring
 have hl:= abs_le.mp (net_gain p c q M P ht hp (e*sites N+k* D) hI); linarith only [hl.2]
end Hours
end YM.CF.Velvet
#print axioms YM.CF.Velvet.Hours.account_cov
#print axioms YM.CF.Velvet.Hours.time_flowers
