import YM.CF.Cour.Basin
import YM.CF.Cour.Rite
import YM.CF.Cour.Route
import YM.CF.Pec.Ora
import YM.CF.Souk.Rayon
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Hors Newt Souk RG Push Pressure
open Next.SectorChange AnalyticBridge.MarginalMultiplier3b1d Next.SectorChange.Wisps
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {ι:Type}[Fintype ι]{B L:Side}{n k j:ℕ}{e t x u C A:ℝ}
variable {p:Clip}{q: Gauge}{c f:Side}
open Pec
local notation "GG"=>group
variable{m X:Side}{T:Roam m X B}{H: Tube group T}{F: Forest T.ratio}{G: Ratio (CSide m B) (CSide X B)}
variable {h:Odd L.val}{Y:Pricing j L h (Thread j)}{P:Grasp Y B e}{K:Teller GG}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma raker(P:Patch)(p:0<t)(C:ℝ)(k:ℕ):∀ᶠ x in atTop, tollE t (cart x P.L)*C ≤ temp x^k:=by
 let b:= t/(4*P.L.val); have hb:0<b:=div_pos p (by positivity)
 filter_upwards [Newt.smallF (n:=k) hb |C|,Work.E01.radiusB_tendsto.eventually_ge_atTop (100000*P.L.val)] with x hg hL
 let L:=cart x P.L; apply le_trans ?_ hg; have h:P.L.val ≤ Stores.till x:=by unfold Stores.till; omega
 have ht' : Stores.till x ≤ 2*P.L.val* L:=by
    have hp:P.L.val ≤ P.L.val * L:= le_mul_of_one_le_right (by positivity) (Nat.div_pos h P.L.property); rw [mul_assoc]; have hx:Stores.till x % P.L.val + P.L.val* L= Stores.till x:=Nat.mod_add_div ..; have hy : Stores.till x % P.L.val < P.L.val:= Nat.mod_lt (Stores.till x) P.L.property; omega
 apply le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _|>.le)); apply mul_le_mul_of_nonneg_right _ (abs_nonneg C); apply Real.exp_monotone
 unfold b; have he:(Stores.till x:ℝ) ≤2*(P.L.val:ℝ)*(L:ℝ):=by exact_mod_cast ht'
 field_simp; linarith -- tune
lemma pierce_B {z z': Fish ι→ℂ} (h:pierce z C)(v:pierce z' A):pierce (z+z') (C+A):=by
 refine ⟨h.1.add v.1,fun i=>?_⟩; unfold Uniform.entry; rw [iteratedFDeriv_add_apply (h.1.of_le (by norm_num)) (v.1.of_le (by norm_num)),_root_.add_apply]; apply (norm_add_le ..).trans (add_le_add (h.2 _) (v.2 _)) -- tune
variable {s a w g:ℝ}
abbrev crownB(T:Roam m X B)(H:Tube group T)(x:ℝ)(O:Msca m X B G e)(p:0<e)(l:ℕ)(α:ℝ)(F:Forest T.ratio)(k:T.Choices)(y:Mast group (More (CSide m B))):ℂ:= fence O p (Stores.till x) (Laic.hats F (flute F (sol T H k x F l) 1 y))-α • secondM H.low (safeD H.down (cart x T.patch.L)) (tint group _ y)
lemma candleX (K:Teller GG)(D:Patch)(d:D.Branches K.bind GG)(p:0<e)(l:ℕ)(hl:2 ≤ l)(W:Uniform.Before GG K.top.width K.top.paths K.j K.bind 5)(ha:0<a)(hv:0 ≤ w)(hn:2 ≤ n):∃ A:ℝ,0<A ∧∀ᶠ x in atTop, ∀{m X: Side}(T:Roam m X B)(H: Tube group T)(F:Forest T.ratio), Cert D K T H x→ Char.sizedP GG D K T H F→ ∀ {G:Ratio (CSide m B) (CSide X B)},T.ratio=ratio G →∀ γ,0<γ → Fleck G p F γ C n→ ∀ O:Msca m X B G e, ∀ (M:Male)(U:Dress (CSide X B))(I:Pride (CSide X B))(R:Pride (CSide m B))(α:ℝ), Tally O (shipA G P M U I R) γ C a w n → (∀ z,Critical F H.high H.up z→ cFoot 3 (myth G F z H.low H.down P M U I R α)) → |α| ≤ g → ∀ k:T.Choices, pierce (crownB T H x O p l α F k) (A*temp x):=by
 obtain ⟨A,hA,J⟩:=dale K D d l yet_one W; obtain ⟨Z,hZ⟩:=Uniform.paint_supply GG 2
 let T:= w*Real.exp (a/2*D.L.val)*countCost (a/2); let a':=K.below; let u:= Stationary.gramCost GG a'.paths*stip GG 1 2 Z a'.width
 have hT:0≤T:=by unfold T; have ht:=Uniform.count_pos (half_pos ha); positivity
 let Q:=2*(T+2*((A+1)*T)+(A*T+A*(A*T))); have hQ:0≤Q:=by unfold Q; positivity
 let U:=Q+1; have ht:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 refine ⟨_,add_pos_of_pos_of_nonneg (show 0<1+|g| by positivity) hQ,?_⟩
 filter_upwards [J,raker D K.below.width_pos u 1, Newt.smallF (n:=3) (half_pos ha) 1,ht.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ), Hors.raises GG D.L l 0 A hA.le] with x hx hB hA' ht' hp hv' m r S H F he hF G hf γ hy hY O M Z' I R α hO hZ' hα k
 let t:=temp x; let D':=A*chit GG D K x l*t^(l+2); let X:=H.down
 have ht:0<t:= Work.E09.temp_pos hp; have hp :0≤ chit GG D K x l:=by unfold chit raised; positivity
 obtain ⟨b,c,s,w'⟩:=he.funds.1.feeds; rw [←he.funds.1.high] at s; rw [← he.funds.1.low] at w'
 obtain ⟨z,h⟩:= W.graph F s he.pace he.funds.1.atStep he.funds.1.knobs
 have hv':D' ≤ t^3:=by
    apply le_trans (b:=A*(chit GG D K x l)*t^4) _ _
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le ht' (by omega)) (mul_nonneg hA.le hp)
    unfold chit; refine le_trans (le_of_eq (b:=A*t*(raised GG D.L ((l+1)*radiusB x)+1)*t^3) (by ring)) ?_; exact mul_le_of_le_one_left (pow_nonneg ht.le _) hv'
 have hD: 0 ≤ D':= by unfold D'; positivity
 have hu:= crisp K D p (Stores.till x) l n k hn he O M Z' I R hO hf hY hy ha hv hA.le hD (hv'.trans (pow_le_one₀ ht.le ht')) (hx S H F he hF z h k) (hZ' z h.critical) ht
 dsimp only at hu -- uh
 let f(y:Mast group (More (CSide m B))):= fence O p (Stores.till x) (Laic.hats F (flute F (sol S H k x F l) 1 y))- α • secondM H.low H.down (tint group _ y)
 have hU f' :flute F (sol S H k x F l) 1 (t•f')=flute F (sol S H k x F l) t f':= by unfold flute; rw [one_smul]
 simp_rw [show ∀ v,flute F (sol S H k x F l) (temp x) v=flute F (sol S H k x F l) 1 (t•v) from fun v=> (hU v).symm] at hu -- tune t
 rw [he.got] at hu -- underlying dependency cast?
 let V:=Real.exp (-(a/2)*↑(Stores.till x)); have hC:V ≤ t^3:=by rw [mul_one] at hA'; exact hA'
 have hL:f ∘ (fun y=>t•y)=(fun y:Mast group (More (CSide m B))=>_) :=rfl
 change pierce (f∘ (fun y=> t•y)) (2*(D'*T+2*D'*((A+1)*T)+(A*(T*V)+A*(A*(T*V))))) at hu -- tune
 have hS:ContDiffAt ℝ 2 f 0:= (rate_b (n:=2) ht f (hu.1.of_le (by norm_num))).of_le (by norm_num)
 have hN:pierce f (Q*t):=by
    refine ⟨hS,fun i=>?_⟩; have hx:= hu.2 i; unfold Function.comp at hx; rw [entry_scale f t i 0 (show ContDiffAt ℝ (2:ℕ) f (t • 0) by rw [smul_zero]; exact hS.of_le (by norm_num)),smul_zero,norm_smul_of_nonneg (pow_nonneg ht.le _)] at hx
    apply le_of_mul_le_mul_left (hx.trans ?_) (pow_pos ht _)
    calc
       _ ≤ 2*(t^3*T+2*t^3*((A+1)*T)+(A*(T*t^3)+A*(A*(T*t^3)))):=by gcongr <;> assumption
       _ = _:=by unfold Q; ring
 let A':=safeD H.down (cart x S.patch.L); let W(y:Mast group (More (CSide m B))):= secondTerm H.low H.down (represent (tint GG _ y))- secondTerm H.low A' (represent (tint GG _ y))
 let L(y):= α • Complex.ofRealCLM (W y)
 have hp(i:Fin 2→ Uniform.Primary (More (CSide m B)) GG):pierce L (|g| *t):=by
    have hq:2≤(More (CSide m B)).val:=by have hq:=he.size; omega
    obtain ⟨hp,hV⟩:=riseP (Λ:=0) Z hZ (cart x S.patch.L) t w' hq i
    let K:= W; have hk : ContDiffAt ℝ 2 W 0:=hp
    let U:= Complex.ofRealCLM ∘ W; have hX: ContDiffAt ℝ 2 U 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ hk
    refine ⟨hX.const_smul α,fun i'=>?_⟩
    have hu:‖Uniform.entry W 0 i'‖≤t:=by
       apply (riseP (Λ:=0) Z hZ (cart x S.patch.L) t w' hq i').2.trans; rw [he.got]; rw [pow_one] at hB; exact hB
    rw [show Uniform.entry L 0 i'=α • Complex.ofRealCLM (Uniform.entry W 0 i') from ?_,norm_smul]; exact mul_le_mul (hα.trans (le_abs_self _)) ((Complex.norm_real _).trans_le hu) (norm_nonneg _) (abs_nonneg g)
    unfold Uniform.entry; rw [show L=α • U from rfl,iteratedFDeriv_const_smul_apply (hX.of_le (by norm_num)),_root_.smul_apply,show U= _ from rfl]; unfold U; rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hk (by norm_num)]; rfl
 have hZ:crownB S H x O p l α F k=f + L:=by ext1 i; change _=_ +L i; unfold f L; change _= _+α • (↑(W i):ℂ); unfold W; rw [Complex.ofReal_sub,smul_sub]; change _-α •(↑(secondTerm _ _ _):ℂ)= _ ; abel -- tune
 rw [hZ]; let Zf:= f+L; constructor
 · have hp':Nonempty SU.group.ColorIndex:=by
      by_contra! hv; letI:IsEmpty SU.group.ColorIndex:=hv; letI:Nontrivial SU.group.Color:=yet_one.nontrivial_color; exact not_subsingleton SU.group.Color inferInstance
   obtain ⟨i⟩:=hp'; exact (pierce_B hN (hp (fun _=> ((0,Exterior.coord 0),i)))).1
 intro j'; exact ((pierce_B hN (hp j')).2 j').trans (by nlinarith only [ht])
end YM.CF.Cour
