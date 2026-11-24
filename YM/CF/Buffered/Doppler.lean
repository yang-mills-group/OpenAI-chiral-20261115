import YM.CF.Buffered.Flute
/-! Uniform ultimate evaluation coupons, drawn after R (before h).
The compared paths will have dimensions varying. Universe m for tile indices for this service. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric NormedSpace Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial Gall RG Scree Tenant Paige Vault Brace Girt Pic
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N : Side}{I : Type*}{C e v a d x:ℝ}
variable {m L: Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e}
variable {hP:Pearl P} {b c K l r ξ:ℝ} (F: Pic.Span hP K b v c l r n)
include F
lemma mrose (U : Fields (CSide m B))(W:Mark (CSide m B))(h:covariant W)(M:Jill.Male) (g:Seat (CSide m B)→ E)(t:Guard (gauge g U.1) e)(k: n ≤ (CSide m B).val)(b:0≤d)(z:0≤ x)
 (u : Gall.Yep d (acts (star (W (simultaneous g U))) (mateK _)) (changeM P (gauge g U.1) M) x): Gall.Yep (45*d) (acts (star (W U)) (mateK _)) (changeM P U.1 M) x:=by
 let N:=CSide m B; have he(A:Bkg (More N)): Lattice.gauge g⁻¹ (gauge g A)=A:=(by rw [windy,inv_mul_cancel,windy_u]); let U':=tradew N g⁻¹; let T:= changeM P (gauge g U.1) M; let t':= (F.plan m k).1; let i:=mateK N; have hp:Pic.Fone U' T=changeM P U.1 M:= Eq.symm (by nth_rw 1 [← he U.1]; exact Hive.honey_x hP F.stmt t' F.p t g⁻¹); have hm:Pic.Fone U' i=i:= Girt.mastC _
 rw [←hp]; let D:=quantU U'; let V:=W (simultaneous g U); have hz: simultaneous g⁻¹ (simultaneous g U)=U:=Prod.ext (he _) (he _)
 have hk: W U=twist D V:= Eq.trans (congrArg W hz.symm) (h _ _)
 rw [hk,←map_star]; nth_rw 1 [← show Pic.Fone U' (mateK N)=mateK N from hm]; rw [show Pic.Fone U' (mateK N)=acts D.val i from rfl,← Fock.swivel]; exact u.jetF b z U' (lurk_n _)

/- tags purchased for all horizons after selection of h (and with q width v).
 keep possible proof of issuing this data separately. Universe 0 for tile. -/
structure Tower (F: Pic.Span hP K b v c l r n) (R:ℕ)(D H C:ℝ)(α t:ℝ)(w i:ℕ): Prop where
 size : 0<t
 loom : 0 < H
 cup : 0 < D
 live : 0 < C
 wear {m:Side} (p:i ≤ (CSide m B).val) (I:Type)[Fintype I][DecidableEq I] (S:Single (CSide m B)→ I)(Q:I→Melody B R)(U:Fields (CSide m B)) (b:Bool) (l:List I)(h:l.Nodup)(u:Payments w S Q) (M:Jill.Male)(g:Seat (CSide m B)→ E)(k:Candle) (δ:ℝ)(v:slowT (Domain m B) k)(z:lawnK (gauge g U.1) (Kea.tax k) δ)(e:0<δ)(x:δ≤1) (y:(CSide m B).val^10*δ≤t) (f:∀ i,LedgerR (CSide m B) j r C (α/8) b (Q i)):
   Gall.Yep H (acts (star (Melody.festival Q b l U)) (mateK _)) (changeM P U.1 M) (D*Kea.angel m P M*α^l.length)
-- correction choices: waive chooses C BEFORE R; toured after R
lemma floored (α:ℝ)(h:0<α) : ∃ C:ℝ,0<C ∧∀ R:ℕ,∃ D H t:ℝ,∃ w i:ℕ,Tower F R D H C α t w i := by
 obtain ⟨Z,G,C,hZ,hG,hC,X⟩:= Cache.waive.{0} F.p F.rP -- universal metavariable
 let u:=α/4; have hu:0<u:=by unfold u; positivity
 refine ⟨C,hC,fun R=>?_⟩
 obtain ⟨a,y,h₁,hY,w,i,K'⟩:= Melody.toured (B:=B) R _ F.p _ F.rP C hC u hu
 let T:= a*(Z+1); have hT:0<T:=by unfold T; positivity
 obtain ⟨s,k,hS,hk,i',U⟩:= Gall.skin_bounds F.stmt hP F.p F.eP hT.le; obtain ⟨N',L⟩:= Pic.sortV F.p r
 let d:=G*c; have hx:=F.cP; have hd:0<d:=mul_pos hG (zero_lt_one.trans_le hx); let D:=d+k*s*d; have he:n+i'+w+N' ≥ w:=by omega
 refine ⟨D,45*T,min s y,i,n+i'+w+N',⟨lt_min hS hY,by positivity,by unfold D; positivity,hC,?_⟩⟩
 intro m p I _ _ S Q R' q ℒ ht f M g t δ v' l' e' hδ δ' E'
 let N:=CSide m B; let W:=simultaneous g R'; let A:=W.1; let F':=skim N t; let u':=Kea.tax t (N:=More N); obtain ⟨u₀,K₁⟩:= F.plan m (by omega); have hp:(N.val:ℝ)^10*δ≤ s:=δ'.trans (min_le_left ..)
 obtain ⟨hW,D',p',T'⟩:= U m (by omega) M A t δ v' e' hδ hp l'
 let V:=changeM (m:=m) P u' M; have hz:=sea_g (P:=P) u₀ (Kea.tax t) (tax_guard _ _ _ F.eP.le) M; rw [show spar j M _ =_ from K₁.2 t F' M] at hz
 have hw:δ≤ y:=le_trans (le_mul_of_one_le_left e'.le (one_le_pow₀ (show 1≤(N.val:ℝ) by exact_mod_cast N.property))) (δ'.trans (min_le_right ..))
 have hb := X N I K₁.1 (L _ K₁.1 (by omega)).2.1 S t F' M V hz (fun i=> (Q i).goal q W) u a 4 hu.le h₁ (fun T D K₀ p v s f' => K' N (by unfold N; omega) K₁ _ S Q q (by rw [show u/2=α/8 from (by unfold u; ring)]; exact E') f W _ _ (fun i=> (l' i).trans hw) _ _ _ _ p _ s f') ℒ ht
 rw [show 4*u=α from (by unfold u; ring)] at hb
 let V':= Kea.angel m P M; have hP:0 < V':= angel_p hP F.stmt u₀ F.p F.eP M K₁; have hz:0≤ D:=by unfold D; positivity
 let Y':= α^ℒ.length; have hA:0≤Y':=by unfold Y'; positivity
 let X':=d*V'*Y'; have hX:0≤X':=by unfold X'; positivity
 have hv: G*iceK j F' M r ≤ d*V':=by unfold d; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (F.powV m (by omega) M _ F').2.1 hG.le
 have hm:= hb.weigh (mul_le_mul_of_nonneg_right hv hA) hT.le; apply mrose F R' (Melody.festival Q q ℒ) (Melody.festival_cov Q q ℒ) M g hW (by omega) hT.le (by change 0≤D*V'*Y'; positivity); have hω:= hm.join (T'.2 _ _ X' hX hm); rw [p',add_sub_cancel] at hω; refine hω.weigh ?_ hT.le; unfold D; rw [add_mul,add_mul (d*_)] -- tune factor scalar order
 apply add_le_add_right; apply (mul_le_mul_of_nonneg_right (show k*(↑N.val:ℝ)^10*δ≤k*s by rw [mul_assoc]; gcongr) hX).trans_eq; unfold X' Y' d V'; ring
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.floored
