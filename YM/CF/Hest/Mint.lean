import YM.CF.Hest.Isle
import YM.CF.Hest.Zen
import YM.CF.Hest.Cup
import YM.CF.Hest.Poet
import YM.CF.Hest.Vera
import YM.CF.Hest.Gust
import YM.CF.Hest.Foy
import YM.CF.Hest.Hull
import YM.CF.Facet.Prima
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N P m X B L:Side}{n k j:ℕ}{e d t x u C:ℝ}
open Newt Hors Souk
open RG Pressure Push AnalyticBridge.LocalGaussianLaws
local notation "GG"=>group
variable{T:Roam m X B}{c b a r w σ:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}{A:Haze m X B G e}{k':T.Choices}{U:nomA m X B→ Op (Single (CSide m B))}
variable {F:Forest T.ratio}{p:Tube GG T}{j' : Odd L.val}{P': Aim (CSide m B)}{J':Aim (CSide X B)}{F':T.Choices}{v:Vox m B→AxisChart GG F}{h:0<e}{J:ℕ}
def shelfH (G:Ratio (CSide m B) (CSide X B))(A:Haze m X B G e)(h:0<e)(x:ℝ) (P:nomA m X B): Op (Single (CSide m B)):=∑ i∈ portA (Stores.till x), A i (Pec.pear G h P)
abbrev teen(F:Forest T.ratio)(p:Tube GG T)(x:ℝ)(k':T.Choices)(l:ℕ)(t:ℝ):= Laic.hats F ∘ flute F (sol T p k' x F l) t
lemma weather (K:Teller GG)(P: Patch)(p:P.Branches K.bind GG)(W:Uniform.Before GG K.top.width K.top.paths K.j K.bind (n+2))(n':3 ≤ n)(t:0<e)(hk:0 < a)(hy:0≤ b)(hq:0 < r)(L:Side)(j':Odd L.val)(j l:ℕ)(hl:1 ≤ l): ∃ Z Y V:ℝ,0<Z∧0≤ Y∧0≤V∧∀ᶠ x:ℝ in atTop, temp x ≤ Z ∧∀ {m X B:Side}(T:Roam m X B)(H:Tube GG T)(F:Forest T.ratio),Cert P K T H x→ Char.sizedP GG P K T H F → ∀ {G}, Fleck G t F r C n →∀ (A:Haze m X B G e) (F':Aim (CSide X B))(P':Aim (CSide m B))(D:Male), Ind G A a b C n (Budget L j' F'.den P'.den G D j)→(∀ z,Critical F H.high H.up z→ cFoot 3 (emergence L j j' G F z D F'.den-flareP L j j' D P'.den)) → ∀ k:T.Choices,∀ d:ℝ,temp x ≤ d→d ≤ Z → ∀ v:Mast GG (More (CSide m B)), ‖v‖<1 →
 let Φ:= flute F (sol T H k x F l) d; (Allows n Φ v (Y*d) ∧ ‖Φ v‖<r ∧ ∀ i j,Allows n (fun y=>shelfH G A t x (teen F H x k l d y) i j) v (V*d^3)):=by
 obtain ⟨a',b',t',A,D',ha,hb,hc,hA,hE,H⟩:=Newt.yields K n l (by omega) P p W; let M:= max 1 (A+b'); have hM:1≤ M:=le_max_left ..; have hV:0<M:=lt_of_lt_of_le one_pos hM; let Y:=3*M
 let r':= min r 1; let Z:= min ((a')/2) (min D' (r'/2 /Y)); have hR:0<r':=lt_min hq one_pos; have hY:0<Y:=by unfold Y; positivity
 have hZ:0<Z:= lt_min (half_pos ha) (lt_min hE (by positivity)); have hz :Y*Z<r':= by rw [mul_comm]; exact ((le_div_iff₀ hY).mp ((min_le_right ..).trans (min_le_right ..))).trans_lt (half_lt_self hR)
 have hs : Z<a':= (min_le_left ..).trans_lt (half_lt_self ha); have hu := hz.trans_le (min_le_right ..); have hx:1 ≤ Y:=by unfold Y; linarith only [hM]
 let V:=Jet.composeCost n b 1; let T:=2^2*Jet.composeCost 2 b 1*b'+Jet.composeCost 2 b 1; refine ⟨Z,Y,3*T+V/Z^3,hZ,hY.le,by unfold V T Jet.composeCost; positivity,?_⟩
 filter_upwards [H,eventually_gt_atTop (0:ℝ), (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds hZ), Newt.smallF (n:=3) hk 1] with x ht hf hp hg
 refine ⟨hp,?_⟩; intro m X B S H F hw hw' G hξ U M₁ M₂ P' p g k d he hd v hv Φ
 obtain ⟨v',hH,hH',hv',hT⟩:=ht S H F hw hw'; let ℓ:=temp x; let J:=sol S H k x F l; let Ψ:= Uniform.station v'; have hℓ:0<ℓ:=Work.E09.temp_pos hf
 have h(v':ℝ)(hs':ℓ ≤ v')(hj:v' ≤ Z):
      let f(y):=J (v'•y); let g(y):=Ψ (v'•y);
      Folded f g n (b'* v'^(l+2)) ∧ ∀ y:Mast GG (More (CSide m B)),‖y‖<1→ Allows n f y (M*v')∧Allows n g y (M*v')∧ Allows n (flute F J v') y (Y*v') ∧‖flute F J v' y‖<r:=by
    intro f g; have ht:0<v':= hℓ.trans_le hs'; have hr:v'≤1:= hj.trans ((le_mul_of_one_le_left hZ.le hx).trans hu.le); have hK:=hT k v' ht hs' (hj.trans ((min_le_right ..).trans (min_le_left ..))); refine ⟨hK,fun i g'=>?_⟩
    have hϕ:Allows n g i (A*v'):=by
       have hx:=Newt.near_s (f:=Ψ) ht.le hr (show 1 ≤ n by omega) (hj.trans_lt hs) (fun y hy=> (hH' y hy.le).2.1) g'.le; rw [show Ψ 0=0 from by unfold Ψ; simp [Uniform.station,hH.critical.1]] at hx; simp_rw [sub_zero] at hx; exact hx
    have he:= Jet.Allows.add (f:=fun y=> f y-g y) (hK.due i g') hϕ; simp_rw [sub_add_cancel] at he
    have hP: Allows n f i (M*v'):=he.mono ((add_le_add_left (mul_le_mul_of_nonneg_left (pow_le_of_le_one ht.le hr (by omega)) hb.le) _).trans (le_trans (le_of_eq (b:=(A+b')*v') (by ring)) (mul_le_mul_of_nonneg_right (le_max_right ..) ht.le)))
    have hV:= (turn_safe hP hP ht.le hM g' 0 (Set.left_mem_Icc.mpr zero_le_one)); have hz': Jet.Allows n (flute F J v') i (Y*v'):= hV.germ (Eventually.of_forall (fun y=>by simp; rfl))
    exact ⟨hP,hϕ.mono (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right hb.le).trans (le_max_right ..)) ht.le),hz',hz'.value.trans_lt ((mul_le_mul_of_nonneg_left hj hY.le).trans_lt (hz.trans_le (min_le_left ..)))⟩
 obtain ⟨hg',hv',hz'⟩:=(h d he hd).2 v hv; refine ⟨hz'.1,hz'.2,fun i j=>?_⟩
 let f(d:ℝ)(y):= shelfH G U t x (teen F H x k l d y) i j -- k ambiguous
 let W:= Real.exp (-a * Stores.till x); have ht:0 < d:=hℓ.trans_le he
 have hv: W ≤ d^3:=(show W*1=W from mul_one _).symm ▸ hg.trans (pow_le_pow_left₀ hℓ.le he _)
 let N:= f 1; have he'(s:ℝ): f s=fun y=> N (s• y):= by funext y; change shelfH G U t x (teen F H x _ l s y) _ _= shelfH G U t x (teen F H x _ l 1 _) _ _; unfold teen Function.comp flute; rw [one_smul]
 have hB(s y): f s y= ∑ u∈ portA (Stores.till x), U u (frameT G t F (flute F J s y)) i j:= Matrix.sum_apply .. -- tune
 have hU: Jet.Allows 2 (f d) 0 (T*d^3):=by
    let hδ:= (h d he hd)
    have hε:=mul_le_mul_of_nonneg_left hd hY.le
    have hb:= xxxA d t p hξ J Ψ rfl ht (g v' hH.critical) n' hk hM (fun i hi=> ⟨((hδ.2 i hi).1).order (by omega), ((hδ.2 i hi).2.1).order (by omega)⟩) (hε.trans_lt (hz.trans_le (min_le_left ..))) (hε.trans hu.le) ((hδ.1.due 0 (by simp)).order (by omega)) i j (Stores.till x)
    rw [funext (hB d)]; apply hb.mono; let C:=composeCost 2 b 1; have hc:0≤C:=by unfold C composeCost; positivity
    have hr:d^(l+2) ≤ d^3:=pow_le_pow_of_le_one ht.le (hd.trans ((le_mul_of_one_le_left hZ.le hx).trans hu.le)) (by omega)
    rw [show composeCost 2 (W*b) 1=C*W by unfold C W composeCost; ring] -- tune
    unfold T; apply le_trans (a:=2^2*C*(_*_) + C*W) _ (le_of_eq (show 2^2*C*(b'*d^3)+ C*d^3=_ by unfold C; ring)); gcongr -- tune
 have hm(y: Mast GG (More (CSide m B)))(hv':‖y‖<1): Jet.Allows n (f Z) y V:=by
    obtain ⟨he,v⟩:= (h Z hp le_rfl).2 _ hv'|>.2.2
    have ht := snick p t F hξ (portA (Stores.till x)) 0 i j hk (fun k _=>Nat.zero_le _) _ v; rw [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] at ht; rw [funext (hB Z)]; exact ht.comp (he.mono hu.le)
 change Jet.Allows n (f d) v _; rw [he' d] at *; apply (lift_e (u:=Z) (fun u v=> by rw [← he' Z]; exact hm u v) ht hd hU n' v (by assumption)).mono
 exact le_of_eq (by unfold T composeCost; field_simp)
end YM.CF.Hest
