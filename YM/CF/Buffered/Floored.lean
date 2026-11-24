import YM.CF.Kea.Cool

/-! Commensurate second-price comparison for *massless*, anti-every-axis
Bloch caps. No lattice-to-continuum approximation of the logs needed. The two
floors in this computation are the SAME real number, hence different in units
of pinch². `punch` pays on the coarser lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Glaze
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {j:ℕ} {M N : Side}
abbrev Snow := Axis → Fin 3

def glacier (N M : Side) (i : Snow × Site N) : Site M :=
 fun a => ((3 * chert (i.2 a) + (i.1 a).val : ℤ): Per M)
private lemma three (h : M.val = 3*N.val) : pinch N = 3 * pinch M := by
 unfold pinch
 push_cast [h]
 ring
private lemma distance_d (h : M.val = 3*N.val) : (M.val:ℤ) = 3 * (N.val:ℤ) := by exact_mod_cast h
lemma glacier_i (h : M.val = 3*N.val) : Injective (glacier N M) := by
 rintro ⟨x,k⟩ ⟨y,l⟩ he
 have hi a := congrFun he a
 have hh(a:Axis) : (M.val:ℤ) ∣ (3*chert (k a)+(x a).val)-(3*chert (l a)+(y a).val) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ..).1 (by rw [Int.cast_sub]; exact sub_eq_zero.mpr (hi a))
 choose f H using hh
 have hx(a:Axis) : (x a).val = (y a).val := by
   have hl := H a
   rw [distance_d h,mul_assoc] at hl
   have hz := (x a).isLt
   have ht := (y a).isLt
   omega
 apply Prod.ext (funext fun a => Fin.ext (hx a))
 funext a
 have hg : (N.val:ℤ) ∣ chert (k a)-chert (l a) := by
   refine ⟨f a,?_⟩
   have hp:= H a
   rw [hx,distance_d h,mul_assoc] at hp
   omega
 have hr:= (ZMod.intCast_zmod_eq_zero_iff_dvd ..).2 hg
 rw [Int.cast_sub,chert_cast,chert_cast] at hr
 exact sub_eq_zero.mp hr

lemma snow_card : Fintype.card Snow = 81 := by simp [Snow,Axis]

def freezes (h : M.val = 3*N.val) : (Snow × Site N) ≃ Site M := Equiv.ofBijective _
 ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨glacier_i h,by simp [Fintype.card_prod,h]; ring⟩)

def frost (N : Side) (i : Snow) : Jill.Offset N :=
 ⟨fun a=> (2/3:ℝ)*( (i a).val-1)*pinch N,
 (pi_norm_le_iff_of_nonneg (pinch_pos N).le).mpr fun a=> by
   change ‖(2/3:ℝ)*( ((i a).val:ℝ)-1)*pinch N‖ ≤ _
   generalize i a = k
   have hp:=pinch_pos N
   fin_cases k <;> norm_num [abs_of_pos hp,hp.le] <;> linarith⟩
lemma glaciers_near (h : M.val = 3*N.val) (x:Snow) (k:Site N) :
 peers (pm k+(frost N x).val) (pm (freezes h (x,k))) := by
 let V:= glacier N M (x,k)
 have he(a:Axis) : (M.val:ℤ) ∣ chert (V a)-(3*chert (k a)+(x a).val) := by
   apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).1
   rw [Int.cast_sub,chert_cast]; exact sub_self _
 choose f H using he
 refine ⟨f,?_⟩; funext a
 change Lat.principal (V a)=Lat.principal (k a)+(2/3:ℝ)*( ((x a).val:ℝ)-1)*pinch N+2*Real.pi*f a
 rw [ch_price,ch_price, eq_add_of_sub_eq (H a), payH (N:=M),three h]
 push_cast; ring

private lemma log_site (r:ℝ) (p:0<r) (N:Side) (A:Jill.Male) :
 Real.log (iceK j (too N) A r)=45 * ∑ x:Site N, Real.log (cup N j A r (pm x)) := by
 rw [iceK,Real.log_prod (fun i _=> (cup_p _ p _).ne')]
 simp_rw [too_u]
 rw [Fintype.sum_prod_type,sum_comm]
 dsimp only
 rw [sum_const,card_univ,slots]; norm_num
private lemma log_slurry (r:ℝ)(A:Jill.Male)(x:Offset N):
 (∑ k:Site N, Real.log (cup N j A r (pm k+x.val)))=slurry N j r A x + ∑ _k:Site N, Real.log (r*pinch N^2) := by
 unfold slurry cold; rw [sum_sub_distrib,sub_add_cancel]
lemma glaciers_sum (r:ℝ) (p:0<r) (v:Even N.val) (w:Even M.val) (h:M.val=3*N.val) (A:Jill.Male) :
 Real.log (iceK j (too M) A (9*r))-81*Real.log (iceK j (too N) A r)=
 45 * ∑ i:Snow,(slurry N j r A (frost N i)-slurry N j r A (zeroF N)) := by
 have he(i:Snow)(k:Site N) : cup M j A (9*r) (pm (freezes h (i,k)))=cup N j A r (pm k+(frost N i).val) := by
   have hg : Bound Real.pi (pm (freezes h (i,k))) := by simpa [zeroF] using orb (freezes h (i,k)) (zeroF M) w
   unfold Jill.cup disk
   rw [(glaciers_near h i k).map_shell (base_subset_realCube zone_pos (b_base (orb k (frost N i) v))) (base_subset_realCube zone_pos (b_base hg))]
   congr 1; rw [three h]; ring
 let F:= fun x:Site M => Real.log (cup M j A (9*r) (pm x))
 let u:=slurry N j r A (zeroF N)
 let l:=∑ _k:Site N, Real.log (r*pinch N^2)
 rw [log_site _ p, log_site _ (by positivity)]
 have hh : (∑ k:Site N, Real.log (cup N j A r (pm k)))=u+l := by simpa only [zeroF,add_zero,u,l] using log_slurry (j:=j) r A (zeroF N)
 rw [hh]
 change 45 * ∑ x:Site M, F x-81*(45*(u+l))=_
 rw [← Equiv.sum_comp (freezes h) F,Fintype.sum_prod_type]
 simp_rw [F,he,log_slurry]
 change 45 * ∑ i:Snow,(slurry N j r A (frost N i)+l)-81*_=_
 rw [sum_add_distrib,sum_sub_distrib,sum_const,sum_const,card_univ,snow_card]
 simp only [nsmul_eq_mul,Nat.cast_ofNat]; unfold u; ring
lemma peel {r:ℝ} (H:1≤j) (p:0<(r:ℝ)) :
 ∃ D:ℝ,0<D∧∀ (N M:Side), M.val=3*N.val → Even N.val → Even M.val → 18*pinch N<zone →∀ A:Jill.Male,
 ‖Real.log (iceK j (too M) A (9*r))-81*Real.log (iceK j (too N) A r)‖≤D := by
 obtain ⟨D,g,t⟩:= punch H p
 refine ⟨45*(81*D),by positivity,fun N M h e e' hv A=>?_⟩
 rw [glaciers_sum _ p e e' h, norm_mul, Real.norm_of_nonneg (by norm_num : 0≤(45:ℝ))]
 refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans ((sum_le_sum (fun i _=> t N e hv A _)).trans_eq ?_)) (by norm_num)
 rw [sum_const,card_univ,snow_card,nsmul_eq_mul,Nat.cast_ofNat]

variable {L B m l:Side} {ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}{P:Grasp Y B e}
lemma angel_floor (p:1 ≤ j) : ∃ r:ℝ,0<r∧∀ s:ℝ,s≤r→∀ B m:Side, ∀ (P:Grasp Y B e)(M:Jill.Male),
  P.roundZ ≤ (CSide m B).val → 0<e → Pad j (CSide m B) → angel m P M=iceK j (too (CSide m B)) M s := by
 obtain ⟨r,v,W⟩:= zipper p (show (0:ℝ)<1 by norm_num)
 refine ⟨r,v,fun s hs B m P M hp hx ht=>?_⟩
 unfold Kea.angel; rw [rich hp hx M ht _ (too _)]
 apply prod_congr rfl; intro i _
 apply Eq.symm; apply max_eq_right
 refine le_trans (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) ?_
 have hi := W _ ht.1 _ (too (CSide m B)) M (empty_m (by norm_num) _) i
 rw [← hi]; exact le_max_left ..

lemma angel_triple (p:1≤j) :
 ∃ C:ℝ,0<C ∧ ∀ (P:Grasp Y B e) (m l:Side), (CSide l B).val=3*(CSide m B).val →
 P.roundZ ≤ (CSide m B).val → P.roundZ ≤ (CSide l B).val → Pad j (CSide m B) → Pad j (CSide l B) → 18*pinch (CSide m B)<zone → 0<e → ∀ A:Jill.Male,
 ‖Real.log (angel l P A)-81*Real.log (angel m P A)‖≤C := by
 obtain ⟨r,v,W⟩:= angel_floor (Y:=Y) (e:=e) p
 obtain ⟨C,q,h⟩:= peel p (show 0<r/9 by positivity)
 refine ⟨C,q,fun P m l hp t z u i b f A=>?_⟩
 rw [W (9*(r/9)) (by linarith) _ _ _ _ z f i,W (r/9) (by linarith) _ _ _ _ t f u]; exact h _ _ hp u.1 i.1 b A
#print axioms angel_triple
end YM.CF.Buffered.Glaze
