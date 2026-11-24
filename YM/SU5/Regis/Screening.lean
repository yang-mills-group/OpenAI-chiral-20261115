import YM.SU5.Regis.Visitations
/-! # Weighted perturb charge chess -/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open Buffered
open CF.Pannier.Damask Lamour.Bridge.Celeste
open YM.CF.Velvet
open Pannier
namespace Papal
open Regis.Head CF.Pannier.Chancel
open Buffered.Afterglow Journey
open Clock Hookah
variable {I:Type*}[Fintype I] (A:Etch SU.group I)(a:ℂ)(t:Geometry P) (p:P.Attic) (u:∃ a',Procurement P.K.j a' P.d)
abbrev budS(A: Etch SU.group I)(a:ℂ)(q:Clip)(z:ℝ):=a.re*z+ plenitude A a + A.aftermath q*a.re^2
include u t p
-- charge per plantation
lemma lens (b:ℕ) (ε:ℝ)(pE:0<ε):∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick≤ k → s ≤ Y.uv k → ∀ (L:List (Hookah (count Y s i))), Hookah.Sylvan A (museumV (P:=P) s) a b L → ‖Journey.compass Y i k s (Hookah.buffet L)‖ ≤ Real.exp (ε*sites (count Y s i)+L.length * budS A a P.K.top.clip (hatsMuseo Y A s i k)):=by
 let S:= ε/9; have hs : 0<S:= by unfold S; positivity
 obtain ⟨m,h⟩:=u; obtain ⟨x,hx,v,L⟩:=crystal_air P.K.j (by rw [P.kJ]; decide) S hs; have hp:= charged_veil.{0} Y A a.re S h hx v hs (L x hx le_rfl) (flow_pos hx).le p t 0 -- universes
 filter_upwards [hp] with s hr; filter_upwards [hr] with i hy k z T L χ; obtain ⟨hz,t',f,hf,E⟩:=χ.chart; let N:=count Y s i; let B:=gram Y s i k; let Z:= budS A a P.K.top.clip (hatsMuseo Y A s i k); let H:= Hookah.buffet L; let P':= poles L;
 have ht:= hy k z T P' t' hz H (L.length*plenitude A a) χ.occupy.env (fun V=>?_)
 swap; · obtain ⟨c,d⟩:=safety Y s i k V; let G:=room Y s i V; let A':=V.1; let F:=H (V.1,G); let Y':=a.re*A.gallery (museumV (P:=P) s) t' P' A'; let b':= L.length*plenitude A a; let D:=tickA N; have hr:D=cutM (Tset N):=touchP N; let Φ:=spar P.K.j B.J.M G; let q:= issue c hx v (S:=Tset N) (show Sea (cutM _) (mateK N) from hr ▸ tickB N) d F; apply q.weigh _ (flow_pos hx).le; rw [←hr]; let S':= trade Φ D x; have hs: ‖modifyB D x F‖ ≤Real.exp (Y'+ b'):=by rw [modifyB, show F=f A' • (1:FC _) from congrFun hf (V.1,G), Matrix.mul_smul,mul_one, Matrix.smul_mul,pushV ( (show IsStarProjection D from hr.symm ▸ cutM_idp _) ) hx,norm_smul,norm_one,mul_one]; exact E _
         change _* Real.exp S' ≤ Real.exp (S'+0*_+(b'+Y')); rw [zero_mul,add_zero]; refine (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le).trans_eq ?_; rw [←Real.exp_add]; congr 1; ring
 apply (broken_ratio Y i s k _).trans (ht.trans_eq ?_); rw [show 9*S=ε from (by unfold S; ring),Fintype.card_fin]; unfold budS; congr 1; ring
omit t p u
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
lemma budget_non (a:ℂ)(s i k:ℕ): let b:= |a.re| *A.arc; -b ≤ budS A a P.K.top.clip (hatsMuseo Y A s i k):=by
 intro b; let x:= hatsMuseo Y A s i k; let U:= budS A a P.K.top.clip x; have ht: |x| ≤ A.arc:=A.stable_budget ..
 have HG:0≤plenitude A a:=by unfold plenitude; positivity
 have hh := abs_le.mp (show |a.re*x| ≤ b from (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _))); change -b ≤ a.re*x+_+_;  linarith only [hh.1,HG,mul_nonneg (A.aftermath_pos (q:=P.K.top.clip)) (sq_nonneg a.re)] -- b unfolded? x
include u t p H
lemma paying (b:ℕ) (ε:ℝ)(pE:0<ε) : ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop,∀ (L:Hookah (count Y s i)), Hookah.Cost A (museumV (P:=P) s) a L → (∀ i,cows i (Lattice.halo 0 L.S) b) → ‖Journey.compass Y i k s L.x‖≤ Real.exp (budS A a P.K.top.clip (hatsMuseo Y A s i k) + 3*ε):=by
 let K:= tent Y H; let B:=4*(b+addgap K)
 have hB:0<B:= Nat.mul_pos (by omega) (Nat.add_pos_right _ (addgap_pos))
 let S:=ε/(B:ℝ)^4; have hS:0<S:= by unfold S; positivity
 let ψ:=-(|a.re| * A.arc); let M:=portraitK A a
 filter_upwards [lens Y A a t p u 0 _ hS] with s hr; filter_upwards [hr,(count_grows Y s).eventually_ge_atTop (b+addgap K)] with i hf hX;
 let N:=count Y s i; let D:= (More N).val ^ 4; let U:=Real.exp ε; have ht:M≥1:=pk_h ..; have hp:0<M:=zero_lt_one.trans_le ht; let E:= min 1 (Real.exp ψ); have hv:0<E:=lt_min one_pos (Real.exp_pos _); let g:= ((U-1)* E^D)/M^D; have he:1<U:=Real.one_lt_exp_iff.mpr pE; have hz:0<U-1:=sub_pos.mpr he; have hg:0<g:=by unfold g; positivity
 filter_upwards [ferry_later Y s i, thaw_plot Y g hg s] with k X V A' D' p'
 obtain ⟨T,t',h₀,h₁,h₃,e⟩:= Hookah.trefoil (revive Y H s i k X) (terrain Y H (Y.ir i) s).symm (show b+addgap K≤ N.val from hX) _ D' p'; let n:=T.length; let x:= budS A a P.K.top.clip (hatsMuseo Y A s i k); let y:= Real.exp (x+ε); have hy:ψ ≤ x:=budget_non ..; have hy': E≤y:=min_le_right .. |>.trans (Real.exp_monotone (hy.trans (le_add_of_nonneg_right pE.le))); have y0:0<y:=Real.exp_pos _
 let F:= Journey.compass Y i k s; 
 let F':= solder Y i k X.depth s; let W:= Hookah.buffet T; have hF:‖F W‖≤ y^n:=by
    refine (hf k X.depth X.enters T t').trans ?_; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; have ht: sites N ≤ (n:ℝ)*(B:ℝ)^4:=by unfold sites; exact_mod_cast h₃ -- h₃ tune
    have he:S*sites N ≤ ε*n:= by refine (mul_le_mul_of_nonneg_left ht hS.le).trans_eq (?_); unfold S; field_simp
    change S*sites N + (n:ℝ)*x≤(n:ℝ)*(x+ε); linarith only [he]
 have ha(c:ℕ)(t:c≤D)(v:Mark N)(H:Envelope v)(u:∀ x,‖v x‖≤ M^D): ‖F v-F' v‖ ≤ (U-1)* y^c:= by
    apply (V i X.depth v (M^D) H u).trans; unfold g; rw [div_mul_cancel₀ _ (pow_pos hp _).ne']; exact mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one hv.le (min_le_left ..) t).trans (pow_le_pow_left₀ hv.le hy' _)) hz.le
 change n≤D at h₁; change 1≤n at h₀;
 have heP: ‖F W-F' W‖ ≤ (U-1)*y^n:= ha n h₁ _ t'.occupy.env (fun x=>(t'.rain x).trans (pow_le_pow_right₀ ht h₁)); change ‖F' A'.x‖^n≤ ‖F' W‖ at e
 have hu : ‖F' A'.x‖≤ U*y:=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by unfold U; positivity) (by omega:n≠0)).1; rw [mul_pow]; refine (e.trans ((norm_sub_rev (F' W) (F W)) ▸ (norm_le_norm_sub_add (F' W) (F W)))).trans ?_ -- change below
    refine (le_trans (add_le_add heP hF) ( (show U ≤ U^n from by simpa only [pow_one] using (pow_le_pow_right₀ (a:=U) ‹1<U›.le h₀)) |> (fun g=> (mul_le_mul_of_nonneg_right g (pow_nonneg y0.le n)).trans' (le_of_eq (by ring))))) -- type? fix names
 have hh: ‖F A'.x -F' A'.x‖≤ (U-1)*y:= by refine (ha 1 (Nat.le_trans h₀ h₁) _ D'.owner.env (fun i=> (D'.early i).trans ?_)).trans_eq (by rw [pow_one]); exact (by simpa only [pow_one] using (pow_le_pow_right₀ ht (Nat.le_trans h₀ h₁)))
 apply (norm_le_norm_sub_add (F A'.x) (F' A'.x)).trans ((add_le_add hh hu).trans ?_)
 change _≤ Real.exp (x+3*ε); rw [show x+3*ε= ε+(ε+(x+ε)) from (by ring),Real.exp_add ε (ε+_),Real.exp_add ε]; change _ ≤ U*(U*y); nlinarith only [mul_nonneg (sq_nonneg (U-1)) y0.le]
omit t p u H
-- Four phases, finite tilt θ and normalized complex letter from solder resonance
abbrev paletteU(A: Etch SU.group I)(ρ:ℝ)(t:Signed)(o:Seat N) : Mark N:= Hookah.chalkOp (fun i=> A.palette ρ t o i)
lemma part_here (i s k:ℕ) (X:Ferry Y s i k) : partitionZ (gram Y s i k) P.U (room Y s i) ≠ 0:=by

 exact X.fire.priceA.valid
lemma recoveredF {i s k:ℕ}(f:Ferry Y s i k) (o:Seat (count Y s i))(t:Signed)(ρ:ℝ){S:Finset (Seat (count Y s i))} (h: AtSupport false S (paletteU A ρ t o))(a:ℂ): let U:=pal A ρ a t o; AtSupport false S U ∧ Journey.compass Y i k s U=1+a*Journey.compass Y i k s (paletteU A ρ t o):=by
 let T:=paletteU A ρ t o; let U:Mark (count Y s i):=1
 intro f'; have hf: f'=U+a • T:=by funext F; change (1+a*(A.palette _ _ _ F.1:ℝ)) • (1:FC _)= 1+a • ((A.palette _ _ _ F.1:ℂ) • 1); rw [add_smul,one_smul, mul_smul]
 have hu:=AtSupport.oneM S; rw [hf]; refine ⟨hu.addM (h.smulM _),?_⟩
 unfold Journey.compass; rw [mark_add (roofage Y i s).bill hu.env (h.smulM a).env (Marks.can_read _ _ _ _ (Y.each_level i k s f.depth f.enters)),mark_smul,add_div]; rw [markvac,mul_div_assoc]; congr 1; exact div_self (part_here Y i s k f)
include p t u H
lemma exp_permit (b:ℕ)(ε:ℝ)(pE:0<ε) : ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop, let N:=count Y s i; ∀ (o: Seat N) (v:Signed){S:Finset (Seat N)},o∈S→ (∀ i,cows i (Lattice.halo 0 S) b)→ AtSupport false S (paletteU A (museumV (P:=P) s) v o) → ‖1+a * Journey.compass Y i k s (paletteU A (museumV (P:=P) s) v o)‖ ≤ Real.exp (budS A a P.K.top.clip (hatsMuseo Y A s i k)+ 3*ε):=by
 filter_upwards [paying Y A a t p u H b ε pE] with s h; filter_upwards [h] with i h; filter_upwards [h,ferry_later Y s i] with k h x N o v S l q p; obtain ⟨hA,e⟩:= recoveredF Y A x o v (museumV (P:=P) s) p a; let y:= Hookah.pal A (museumV (P:=P) s) a v o; rw [← e]; exact h ⟨y,S,o⟩ ⟨hA,l,v,a,Or.inl rfl,rfl⟩ q
omit t p u H
lemma candle_fit {ε:ℝ} (q:Clip)(e:0<ε) : ∀ᶠ t:ℝ in 𝓝[>] 0,∀ (z:ℝ), |z| ≤ A.arc → ∀ a:ℂ, ‖a‖=t → Real.exp (budS A a q z + 3*t^2) ≤ 1+a.re*z+t*ε:=by -- ε implicit unresolved?
 let u:= A.arc; let C:= u^2+A.aftermath q+3; have he:=A.arc_non; let k:=u+C; have hb:=A.aftermath_pos (q:=q); have hc:0≤C:=by unfold C; positivity
 have hf:0≤k:= add_nonneg he hc
 filter_upwards [eventually_nhdsWithin_of_eventually_nhds ((continuous_id.mul continuous_const).continuousAt.tendsto.eventually (ge_mem_nhds (show (0:ℝ)*k<1 from (by simp)))),eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one), self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ)) (a:=(0:ℝ)),eventually_nhdsWithin_of_eventually_nhds ((continuous_id.mul continuous_const).continuousAt.tendsto.eventually (ge_mem_nhds (show (0:ℝ)*(k^2+C) < ε from (by simpa using e))))] with t hx ht hv h z hZ a p
 let D:= budS A a q z+3*t^2; change t*k ≤1 at hx; change t*(k^2+C)≤ ε at h; have hz:0<t:=hv; let w:= a.re*z; let B:=w+t^2*C; have hh: |a.re| ≤ t:=p ▸ Complex.abs_re_le_norm a
 have hg: |w| ≤ t*u:=by unfold w; rw [abs_mul]; exact mul_le_mul hh hZ (abs_nonneg _) hz.le
 have hu: D ≤ B:=by
    unfold D budS plenitude B C; change _ + _ ≤ w+ t^2*_ ; rw [p]; have hw:a.re^2 ≤ t^2:=sq_abs a.re ▸ pow_le_pow_left₀ (abs_nonneg a.re) hh _; unfold w u; linarith only [mul_le_mul_of_nonneg_left hw hb]
 have hk:|B| ≤ t*k:=by unfold B k; apply le_trans (abs_add_le ..); rw [abs_of_nonneg (show 0≤ t^2*C from mul_nonneg (sq_nonneg _) hc)]; rw [mul_add t u C]; refine add_le_add hg (mul_le_mul_of_nonneg_right ?_ hc); nlinarith [ht]
 have hp:= le_trans (le_abs_self (Real.exp B-1-B)) (Real.abs_exp_sub_one_sub_id_le (hk.trans hx)); apply (Real.exp_monotone hu).trans; change Real.exp B ≤ 1 + w + _; linarith only [hp, (pow_le_pow_left₀ (abs_nonneg B) hk 2), sq_abs B, show B=w+t^2*C from rfl, mul_le_mul_of_nonneg_left h hz.le]
lemma cronus (q:Clip)(b c D:ℝ)(z:ℂ)(h:0<c)(aB: ‖1+(c:ℂ)*z‖≤1+c*b+c*D)(xB: ‖1-(c:ℂ)*z‖≤1-c*b+c*D)(u: ‖1+(c:ℂ)*Complex.I*z‖≤1+c*D)(v: ‖1-(c:ℂ)*Complex.I*z‖≤1+c*D) : ‖z-(b:ℂ)‖≤2*D:=by
 let p(x:ℂ):= Complex.re_le_norm x; -- syntax let p uses h choice?
 have h1:= (p (1+(c:ℂ)*z)).trans aB; have h2:= (p (1-(c:ℂ)*z)).trans xB; have h3:= (p (1+(c:ℂ)*Complex.I*z)).trans u; have h4:= (p (1-(c:ℂ)*Complex.I*z)).trans v
 simp only [Complex.add_re,Complex.sub_re,Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero,zero_sub] at h1 h2 h3 h4
 apply (Complex.norm_le_abs_re_add_abs_im _).trans; simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]; rw [two_mul]; apply add_le_add <;> apply abs_le.mpr <;> constructor <;> nlinarith only [h,h1,h2,h3,h4] -- need strict branch linear?
include t p u H
lemma lens_state (b:ℕ)(ε:ℝ)(pE:0<ε) : ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop, let N:=count Y s i; ∀ (o: Seat N) (v:Signed){S:Finset (Seat N)},o∈S→ (∀ i,cows i (Lattice.halo 0 S) b)→ AtSupport false S (paletteU A (museumV (P:=P) s) v o) → ‖Journey.compass Y i k s (paletteU A (museumV (P:=P) s) v o) - (hatsMuseo Y A s i k:ℂ)‖ ≤ ε:=by
 let e:=ε/2; let q:=P.K.top.clip; have he:0<e:=half_pos pE; obtain ⟨δ,f,h⟩:= ((candle_fit A q he).and self_mem_nhdsWithin).exists; change 0 < δ at h; let K(z:ℂ):=exp_permit Y A z t p u H b (δ^2) (pow_pos h _)
 let w:ℂ:=δ; let T':=w*Complex.I
 filter_upwards [K w,K (-w), K T', K (-T')] with s h1 h2 h3 h4; filter_upwards [h1,h2,h3,h4] with i h1 h2 h3 h4; filter_upwards [h1,h2,h3,h4] with k h1 h2 h3 h4 N o v S z L hψ
 let A':= hatsMuseo Y A s i k; let Z:= Journey.compass Y i k s (paletteU A (museumV (P:=P) s) v o)
 have hz(v:ℂ)(h:‖v‖=δ):= f A' (A.stable_budget ..) v h; have hw: ‖w‖=δ:=by unfold w; rw [Complex.norm_real,Real.norm_of_nonneg h.le]
 have ht: ‖T'‖=δ:=by unfold T'; rw [norm_mul,hw,Complex.norm_I,mul_one]
 apply (cronus q A' δ e Z h ((h1 o v z L hψ).trans (hz w hw)) ?_ ?_ ?_).trans_eq (show 2*e=ε from (by unfold e; ring))
 · have hg:=(h2 o v z L hψ).trans (hz (-w) (by rw [norm_neg,hw])); simp only [neg_mul,Complex.neg_re,sub_eq_add_neg,w,Complex.ofReal_re] at hg ⊢; exact hg
 · have hg:=(h3 o v z L hψ).trans (hz T' ht); rwa [show T'.re=0 from (by simp [T',w]),zero_mul, add_zero] at hg
 have hg:=(h4 o v z L hψ).trans (hz (-T') (by rw [norm_neg,ht])); rw [show (-T').re=0 from (by simp [T',w]),zero_mul, add_zero,neg_mul] at hg; rw [sub_eq_add_neg]; exact hg -- sub isn't defeq
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.paying

#print axioms YM.CF.Py.Rate.LocalLimit.Papal.lens_state
