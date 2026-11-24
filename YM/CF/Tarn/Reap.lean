import YM.CF.Tarn.Open
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tarn
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange
open Neige FreeResolvent.TestD Souk Slate
variable {D d' V' m:ℝ}{e:Directions G c}{u:E}{f₀:E→Directions G c}
lemma ripe (n:ℕ)(K:Teller SU.group)(P:Patch)(p:P.Branches K.bind SU.group): ∃ C m a v θ:ℝ,0<C∧0 < m ∧0<a ∧ 0<v∧ 0<θ∧∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube SU.group S)(F:Forest S.ratio), Cert P K S T x → ∀ (k:S.Choices)(s:ℝ), s∈Set.Icc 0 a → ∀u:Mast SU.group c, ‖u‖<1 →
 let A:=bareStores S; let V:= satU (c:=c) SU.group s
 FreeResolvent.Gap (baseX T x A F k (V u)) m ∧ PriceW (emptyA T x k A F ∘ V) (perZ T x k A F∘ V) n u C (C*tipPay θ x) ∧ PriceW (neo T x k A F∘ V) (simplest (neo T x k A F ∘ V)) n u (C*tipPay v x) (C*tipPay v x):=by
 let G₀:=SU.group
 obtain ⟨a,d,v,C,m,ha,hd,hv,hC,hm,H⟩:=stampX n G₀ K P p
 let D:= room d (C+1) (min m 1) n; let V:=priceFiber P G₀ D; let η:=min m 1; let θ:=↑(n+1:ℕ)*D; let R:= Push.Uniform.shade G₀
 have hP: Price d (C+1) η D 1 V 1 n:=⟨lt_min hm zero_lt_one,by positivity,hd,rfl,le_rfl,(priceFiber_pos ..).le,zero_le_one,le_rfl⟩
 have hz:=hP.pos; let X:= V*meter n n (C+1) 1 (rise V η); let Z:= Jet.composeCost n (activation G₀ n 0 D * FreeResolvent.tagPrice 1 n (C+1) X) R; let M:= Jet.composeCost n (activation G₀ n 0 d*C) R; let S:=2^n*(M+1)*Jet.composeCost n (activation G₀ n 0 D*X) R; let Q:= max (max (max S Z) M) 1; have hM: M ≤ Q:=(le_max_right ..).trans (le_max_left ..)
 refine ⟨Q,m,min a 1,v,θ,zero_lt_one.trans_le (le_max_right ..),hm,lt_min ha zero_lt_one,hv,by unfold θ; positivity,?_⟩
 filter_upwards [H,Work.E01.radiusB_tendsto.eventually_ge_atTop 120, (show Tendsto (fun x=> Q*tipPay v x) atTop (𝓝 (0:ℝ)) by simpa using (tip_s hv).const_mul Q).eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/2))] with x H hp hh c f T U F Q' k t ht u hu A V'
 have hs:t ≤ 1:=ht.2.trans (min_le_right ..); have hA: (bareStores T).flags=RG.flags (temp x) (1:Config G₀ c):=(PhysicalNext.JointLoad.Heir.noFlags ..).symm
 let L:= t • hull G₀ c; let B:= AnalyticBridge.SectorAffine.field (1:Config G₀ c); let f:= B ∘ reader G₀ c ∘ L
 have hv': f=V':=by funext i; unfold V' satU f; rw [Function.comp_apply,Function.comp_apply]; unfold B; rw [reader_field,show L i= hull G₀ c (t • i) from (map_smul (hull G₀ c) t i).symm]
 have he: ‖reader G₀ c (L u)‖≤a:=by
    rw [show L u= hull G₀ c (t • u) from (map_smul (hull G₀ c) t u).symm]; apply (hull_h _).trans; rw [norm_smul_of_nonneg ht.1]; exact (mul_le_of_le_one_right ht.1 hu.le).trans (ht.2.trans (min_le_left ..))
 have hR:(FreeResolvent.native c).Volume (front (G:=G₀) A F (x:=x)) D V:=by unfold V; rw [← Q'.got]; exact (fiber_volume T G₀ hz A F x).1
 obtain ⟨hg,hρ,hL,hV⟩:=H T U Q'.got Q'.size Q'.funds.1 A F k 1 hA (reader G₀ c (L u)) he
 have hf: ‖L‖ ≤ R:=by unfold L; erw [norm_smul,Real.norm_of_nonneg ht.1]; exact (mul_le_mul_of_nonneg_left (show ‖hull G₀ c‖ ≤ R from hull_n) ht.1).trans (mul_le_of_le_one_left (Push.Uniform.shade_pos G₀).le hs)
 have hl:= Jet.allows_linear (n:=n) (L:=L) (x:=u) hf ((L.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hu.le).trans hf))
 rw [←hv']; refine ⟨hg,(coverZ (T:=U) (k:=k) (V:=1) (G:=G₀) hρ hg hm hd hC.le hp hP hR hl rfl).cheaper (show S≤ Q from ((le_max_left ..).trans (le_max_left ..)).trans (le_max_left ..)) ?_,up_p ?_ hh⟩
 · apply le_trans (le_of_eq (_: _= Z*tipPay θ x)) (mul_le_mul_of_nonneg_right (((le_max_right ..).trans (le_max_left ..)).trans (le_max_left ..)) (Real.exp_pos _).le); unfold Z θ tipPay X composeCost; rw [neg_mul]; ring
 apply ((polar_cash _ _ hV (mul_nonneg hC.le (Real.exp_pos _).le) hd).comp hl).mono; exact (le_of_eq (show _= M*tipPay v x from by unfold M composeCost tipPay; ring)).trans (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)
structure Medal (T:Tube SU.group S)(x C m θ a v:ℝ)(n l:ℕ)(t:ℝ)(F:Forest S.ratio)(k:S.Choices)(u:Mast SU.group c): Prop where
 gap: FreeResolvent.Gap (baseX T x (bareStores S) F k (satU SU.group t u)) m
 headX: PriceW (emptyA T x k (bareStores S) F ∘ satU SU.group t) (perZ T x k (bareStores S) F ∘ satU SU.group t) n u C (C*tipPay θ x)
 stepX: PriceW (neo T x k (bareStores S) F ∘ satU SU.group t) (simplest (neo T x k (bareStores S) F ∘ satU SU.group t)) n u (C*tipPay v x) (C*tipPay v x)
 spend(q:Chi)(d':ℝ):let p:= acc T x k (bareStores S) F q d' 1 l ∘ satU SU.group t; PriceW p (simplest p) n u (a*t) (a*t)
lemma spitM (K:Teller SU.group)(P:Patch)(p:P.Branches K.bind SU.group)(hp:2 ≤ n)(hl:l ≤18)(W: Push.Uniform.Before SU.group K.top.width K.top.paths K.j K.bind (n+3))(V:Push.Uniform.Before SU.group K.top.width K.top.paths K.j K.bind (n+2)):
 ∃ C m θ v u r:ℝ,0<C∧0 < m∧0<θ∧0<v∧0<u∧0<r ∧∀ᶠ x in atTop,lamp x ≤ r ∧ ∀ {c f:Side}(S:StepData c f)(T:Tube SU.group S)(F:Forest S.ratio), Cert P K S T x→ sizedP SU.group P K S T F→ ∀ (k:S.Choices)(s:ℝ),lamp x ≤ s→ s ≤ r → ∀ y:Mast SU.group c, ‖y‖<1→ Medal T x C m θ u v n l s F k y:=by
 obtain ⟨Z,b,hZ,hb,h⟩:=persp K P p n l hp hl W V; obtain ⟨C,m,a,v,θ,hC,hm,ha,hv,hθ,H⟩:= ripe n K P p
 let u:=max (varyP n Z) 1; let r:=min (min (min a b) (1/2/u)) 1; have hu:0<u:=zero_lt_one.trans_le (le_max_right ..); have hr:0<r:=lt_min (lt_min (lt_min ha hb) (div_pos (by norm_num) hu)) zero_lt_one
 refine ⟨C,m,θ,v,u,r,hC,hm,hθ,hv,hu,hr,?_⟩
 filter_upwards [h,H,lamp_s.eventually (ge_mem_nhds hr)] with x hx hH hu'
 refine ⟨hu',?_⟩; intro c f S T F hp' hp'' k s ht hz y hy
 have hs:=hx.1.trans_le ht; have he:=hz.trans (min_le_left ..); have he':=he.trans (min_le_left ..)
 obtain ⟨hg,hp,hz'⟩:=hH S T F hp' k s ⟨hs.le,he'.trans (min_le_left ..)⟩ y hy
 refine ⟨hg,hp,hz',?_⟩; intro q d p; have ht:= (hx.2.2.2 S T F hp' hp'' k s ht (he'.trans (min_le_right ..)) _ hy).flame q d
 exact up_p ((pitchM ht.2.2.1 hZ.le hs.le (hz.trans (min_le_right ..))).mono (mul_le_mul_of_nonneg_right (le_max_left ..) hs.le)) ((mul_comm ..).trans_le ((le_div_iff₀ hu).mp (he.trans (min_le_right ..)))) -- tune
end YM.CF.Tarn
