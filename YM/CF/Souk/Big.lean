import YM.CF.Souk.Kiosk
import YM.Planned.STATIONARY_JET_PORT.InUse
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort
open AnalyticBridge.GaussianFieldAlignment
section seed
variable (T:Tube G S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(q:Chi)(d s:ℝ) (l:ℕ)
abbrev ζ₁(u:Mast G c) := (majorX T x (bareStores S) F k q d 1 l (facadeX G (s • u))).submatrix (pageX F x) (pageX F x)
abbrev μ₁(u:Mast G c) := (layX T x (bareStores S) F k q d 1 l (facadeX G (s • u))).submatrix (pageX F x) (pageX F x)
abbrev ξ(z:fieldDir G c 1→AxisChart G F)(u:Mast G c):=inside k T.high T.up z (s • u)
variable {T x k q d s l}
lemma blossom (V:Config G c): majorX T x (bareStores S) F k q d 1 l V= Relative.symPart (headed T x V k (bareStores S) F (orbitP T x V k (bareStores S) F q d 1 l)):=by ext i j; unfold majorX hessN; simp [green,bareStores,Stores.dome,Stores.place,halo_spec]; rfl -- tune
lemma notSym {f:Fish (ι⊕τ)→ℝ}{p:Fish (ι⊕τ)} {σ: Type}[Fintype σ](u:τ≃σ){M:Neige.Shelf σ}(h: M.submatrix u u=block f p)(hp:ContDiffAt ℝ ω f p): (Relative.symPart M).submatrix u u=block f p:=by
 ext i j; simp only [Relative.symPart,Matrix.submatrix_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply]; rw [show M (u i) (u j)=block f p i j from congrFun (congrFun h _) _, show M (u j) (u i)=block f p j i from congrFun (congrFun h _) _, (isHermitian_iff_isSymm.mp (Uniform.block_hermitian hp)).apply j i,smul_eq_mul]; ring -- orientation?
end seed
variable (G) in
private def rowFare(v:ℝ)(n:ℕ):= (1+Uniform.townCost G*countCost v)^(n+1)
lemma base_high (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(i l:ℕ)(hi:2 ≤ i)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (i+3)):
 ∃ C ε:ℝ, 0<C∧0<ε∧∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F → ∃ z,W.Service F T.high T.up z ∧∀(k:S.Choices)(q:Chi)(d s:ℝ),0<s → temp x ≤ s→ s ≤ ε → ∀ y:Mast G c,‖y‖<1→ Protected i (ξ T F k s z-ζ₁ T F x k q d s l) y (C*s^(l+2)) ∧ ((ξ T F k s z y)-(ζ₁ T F x k q d s l y)).IsSymm:=by
 obtain ⟨a,Q,v,D,p',ha,hQ,hv,hD,hb,H'⟩:= yields K (i+1) l (by omega) P p W
 obtain ⟨t,b,hT,ht,H⟩:= cup (i+1) l (by omega) P K p W
 let A:=max D t; have he:1 ≤ A:=hT.trans (le_max_right ..); have he':0<A:=zero_lt_one.trans_le he
 obtain ⟨u,h,C,hu,hh,hC,hM⟩:=mat_paid K P (i+3) (by omega) W; obtain ⟨hx,H''⟩:=tip_left (i+2) (l+2) P K
 let B:=min (min u a) 1; have hB:0<B:=lt_min (lt_min hu ha) zero_lt_one; let ε:=min (min p' b) (B/(6*A)); have hε:0<ε:=lt_min (lt_min hb ht) (by positivity)
 let X:=C*rowFare G h (i+1); let r:= peak (i+2) P K; let M:=rowFare G r i; let E:= 2^i*composeCost i X 1 * Q + composeCost i M 1
 refine ⟨max E 1,ε,zero_lt_one.trans_le (le_max_right ..),hε,?_⟩
 filter_upwards [H',H,H''] with x hz he0 he''
 intro c f S T F hw hw'; obtain ⟨z,hZ,p₀,ht',hJ⟩:=hz S T F hw hw'; refine ⟨z,hZ,?_⟩; intro k q d s hs hp hk y hy
 obtain ⟨hr,hg⟩:= he0 S T F hw hw' s hs hp (hk.trans ((min_le_left ..).trans (min_le_right ..))) l le_rfl
 let Z(y:Mast G c):= Uniform.station z (s•y); let m(y:Mast G c):=sol S T k x F l (s•y)
 have hE:3*A*s<B:=by have hL: s*(6*A) ≤ B:= (le_div_iff₀ (show 0<6*A by positivity)).1 (hk.trans (min_le_right ..)); linarith
 have hL:s<B:=lt_of_le_of_lt (by nlinarith only [he,hs,mul_le_mul_of_nonneg_right he hs.le]) hE; have hW:3*A*s ≤ 1:=hE.le.trans (min_le_right ..)
 have h₁ (y:Mast G c)(hy:‖y‖<1): Allows i Z y (A*s):=by
    have hh:= near_s (f:=Uniform.station z) hs.le (hL.le.trans (min_le_right ..)) (le_trans (by omega) hi) (show s<a from hL.trans_le ((min_le_left ..).trans (min_le_right ..))) (fun x hx=> (p₀ x hx.le).2.1.order (show i ≤ i+1 from by omega)) hy.le
    simp_rw [show Uniform.station z 0=0 from by simp [Uniform.station,hZ.critical.1],sub_zero] at hh; exact hh.mono (mul_le_mul_of_nonneg_right (le_max_left ..) hs.le)
 have h₂(y:Mast G c)(hy:‖y‖<1): Allows i m y (A*s):= ((hr.root k y hy).order (by omega)).mono (mul_le_mul_of_nonneg_right (le_max_right ..) hs.le)
 let f:=costP F k T.high T.up; let f':= clipped T x F k; let L(y:Mast G c):=meetVar (s•y) (Z y); let U(y:Mast G c):=meetVar (s•y) (m y)
 have hH(y:Mast G c)(hy:‖y‖<1)(f:Mast G c→Fish (Key F G))(h:Allows i f y (A*s)): Allows i (fun y=>meetVar (s•y) (f y)) y (3*A*s):=(turn_safe h h hs.le he hy 0 (left_mem_Icc.mpr zero_le_one)).germ (Eventually.of_forall fun i=>by simp)
 have hI u (hu:‖u‖<B):=(((hM S T x hw).2.2.2 F k).2 u (hu.trans_le ((min_le_left ..).trans (min_le_left ..))))
 have hZ u (hu:‖u‖<B):Wax (f-f') u (i+2) r (s^(l+2)):= (he'' S T hw F k u (hu.trans_le (min_le_right ..))).mono (pow_le_pow_left₀ (Work.E04.temp_nonneg x) hp (l+2))
 let H':=fun (y:Mast G c)=> block f (L y); let P':=fun (y:Mast G c)=> block f' (U y)
 have hh y(hy:‖y‖<1): ζ₁ T F x k q d s l y=P' y ∧ ξ T F k s z y=H' y ∧ paintO (block (f-f') (U y))=paintO (block f (U y))-paintO (P' y) ∧ (H' y).IsSymm ∧ (P' y).IsSymm:=by
    have hx:= (hH y hy _ (h₂ _ hy)).value.trans_lt hE; have hz:= (hI (L y) ((hH y hy _ (h₁ _ hy)).value.trans_lt hE)).1; have he:= (hI _ hx).1; have hp:= (hZ _ hx).1; have h₃: ContDiffAt ℝ ω f' (U y):=by rw [←sub_sub_cancel f f']; exact he.sub hp
    refine ⟨?_,?_,block_minus (F:=F) he hp, isHermitian_iff_isSymm.mp (Uniform.block_hermitian hz), isHermitian_iff_isSymm.mp (Uniform.block_hermitian h₃)⟩
    · unfold ζ₁; rw [blossom]; exact notSym (pageX F x) (hg q d 1 k y hy).2 h₃
    unfold ξ; rw [along_block]; exact (block_identity k T.high T.up _ hz).symm
 let V(z):=paintO (block f z); have hv(w)(hw:‖w‖<B): Allows (i+1) V w X:=stiffness (hI w hw).hv (hI w hw).he (Uniform.town F) hC.le (show 0<h from by assumption)
 have hUq:=hJ k s hs hp (hk.trans ((min_le_left ..).trans (min_le_left ..))); have htV:= varying (m:=m) (z:=Z) hv hy (fun y hy=>⟨h₂ y hy,h₁ y hy⟩) hs.le he hE hW ((hUq.due _ hy).order (show i ≤ i+1 by omega)); have he:Allows i U y (3*A*s):=hH y hy _ (h₂ y hy); have hZ:=hZ (U y) (he.value.trans_lt hE); have hF:= ((stiffness hZ.hv hZ.he (Uniform.town F) (pow_nonneg (show 0 ≤ s from hs.le) _) hx).comp (f:=U) (he.mono hW)) -- tune
 have hK:=hh _ hy; rw [hK.1,hK.2.1]; refine ⟨(subtract_p hF htV).germ ?_ |>.mono ?_,hK.2.2.2.1.sub hK.2.2.2.2⟩ -- tune
 · filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with a (ha:a∈ball _ _); obtain ⟨ha,hb,hc,u⟩:=hh _ (mem_ball_zero_iff.mp ha); dsimp only at * -- tune
   change paintO _-(V (U a)-V (L a))= paintO (_- _); rw [map_sub,hb,ha,hc]; change _-(V (U a)-paintO (H' a))=_; unfold H' U V; abel
 · calc
    _ = E*s^(l+2):=by unfold E X Jet.composeCost M r rowFare; ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg hs.le _)
end YM.CF.Souk
