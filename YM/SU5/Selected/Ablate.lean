import YM.SU5.Selected.Flights
import YM.SU5.FiniteGaugeData.Signal.Polling -- only displacement prior of one city -- no use of Signal law
/-! # Coherent mixed sensor cost on curved configurations of the PHYSICAL links

Fixed physical face(s) in current support. OPTIONAL consultation can pick any
additional faces elsewhere but here no need enlarge support lower proof. Does not assert large
curvature in continuum units, κ for one s and can be arbitrarily tiny. Inhibits completely
within that price. Proof: the transfer op sees pointwise convergence on participating
periods with *pair link* argument drawn from city, not just continuous
sup gauge nor using positive-measure property of vacuum. No delta
support hidden in even a selected cap. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Tapestry (Swatch)
open CF.Pannier.Chancel (Sen booty payout Filigree Lode)
open Set Reliance.ShortWave

private lemma e_multCoeff {A':Finset Cover}{f g:PairsC→ℂ}(p:Coeff false A' f)(q:Coeff false A' g): Coeff false A' (f*g):=by
  obtain ⟨F,h,rfl⟩:= p.narrow rfl
  obtain ⟨G,h',rfl⟩:= q.narrow rfl
  have hv: F ∘ Prod.fst*(G ∘ Prod.fst)=(F*G)∘(Prod.fst:PairsC→ LinksC):= rfl
  rw [hv]; exact Coeff.fromC _ _ (h.mul h') fun x y v=> congrArg₂ (· * ·) (show F x= F y from p.locus (x,x) (y,y) v v) (show G x=G y from q.locus (x,x) (y,y) v v)
private lemma e_multScalar {J:Calibration}{f g:PairsC→ℂ}: scalar J f * scalar J g=scalar J (f*g):= by
  funext m x; change (((_:ℂ) • (1:FC (Single (J.c m))))) * ((_:ℂ) • (1:FC (Single (J.c m)))) = ((_ * _:ℂ)) • (1:FC (Single (J.c m))); rw [mul_smul,Algebra.smul_mul_assoc,one_mul]
lemma preserveFil (J:Calibration)(z:SU.Slot)(S:Finset Cover){q:ℕ}{b:Fin q→ Cover}
    {f:PairsC→ℂ}(p:Coeff false S f){g:Family J}(t:g∈ Filigree J (Window.family z) b S):
    scalar J f*g ∈ Filigree J (Window.family z) b S:= by
  induction t using Submodule.span_induction with
  | mem g p'=> obtain ⟨a,l,h,q,rfl⟩:=p'; rw [← mul_assoc,e_multScalar]; exact Submodule.subset_span ⟨_,_,h,e_multCoeff p q,rfl⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b e h q t => rw [mul_add]; exact Submodule.add_mem _ q t
  | smul a b u v=> rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ _ v

variable (J:Calibration)(S:Finset Cover)(U:Finset (Face ℤ))(n:ℕ)
-- v_n decreasing aperture, no threshold hypothesis. examples
noncomputable def aperture : ℝ:=1/(n+1)
lemma aperture_pos : 0<aperture n:=by unfold aperture; positivity
noncomputable def lit (x:ℝ):ℝ:= min 1 (max 0 (((n:ℝ)+1)*x-1))
private lemma lit_cont : Continuous (lit n):=by unfold lit; fun_prop
private lemma lit_props (x:ℝ):0≤lit n x∧lit n x≤ 1:= ⟨le_min zero_le_one (le_max_left ..),min_le_left ..⟩
lemma lit_low {x:ℝ} (h:x ≤ aperture n): lit n x=0:=by
 unfold lit; rw [max_eq_left,min_eq_right zero_le_one]; apply sub_nonpos.mpr; rw [mul_comm]; exact (le_div_iff₀ (by positivity : 0<(n:ℝ)+1)).1 h
private lemma lit_keep {x:ℝ} (h:0<x):∀ᶠ n in atTop,lit n x=1:=by
  obtain ⟨N,p⟩:= exists_nat_ge (2/x)
  filter_upwards [eventually_ge_atTop N] with n u
  have h' : 2 ≤ (n:ℝ)*x:= (div_le_iff₀ h).mp (p.trans (by exact_mod_cast u))
  unfold lit; rw [min_eq_left]; exact le_trans (show 1 ≤ ((n:ℝ)+1)*x-1 by nlinarith) (le_max_right ..)

noncomputable def rawCut (c:Face ℤ) (x: LinksC):=lit n (SU.group.chord (faceValue x c))
noncomputable def obstruct (x:PairsC):ℂ := ↑(∏ c∈ U, rawCut n c x.1)
noncomputable def curved (f:Family J):=scalar J (obstruct U n)*f
lemma cutC (w:restsOn U S): Coeff false S (obstruct U n):=by
  let F(x:LinksC):= ∏ c∈ U, rawCut n c x
  apply Coeff.fromC (f:=fun x=> ((F x:ℝ):ℂ)) false S (Complex.continuous_ofReal.comp (continuous_finsetProd _ (fun i _=>(lit_cont n).comp (SU.group.continuous_chord.comp (continuous_travel ..)))))
  intro x y hc; apply congrArg; apply Finset.prod_congr rfl; intro i hp
  have he : faceValue x i=faceValue y i:= travel_local i.1 _ x y (fun k v u => hc k (w i hp (List.mem_toFinset.mpr v)) (w i hp (List.mem_toFinset.mpr u)))
  unfold rawCut; rw [he]
lemma obstructPay (x:PairsC): ‖obstruct U n x‖ ≤ 1:= by
  have h:0≤∏ c∈U,rawCut n c x.1:=prod_nonneg fun i v=>(lit_props ..).1
  unfold obstruct; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h]; exact Finset.prod_le_one (fun i v=>(lit_props ..).1) (fun i v => (lit_props ..).2)
lemma obstructRep (f:Family J)(u:Side)(x:Fields (J.c u)): curved J U n f u x= (obstruct U n (onC _ x.1,onC _ x.2)) • f u x:=by change (_ • (1:FC (Single _))) * _=_; rw [Algebra.smul_mul_assoc,one_mul]
lemma stops (f:Family J)(u:Side)(x:Fields (J.c u)){c:Face ℤ}(t:c∈U)(p:SU.group.chord (faceValue (onC _ x.1) c)≤ aperture n): curved J U n f u x=0:=by
  rw [obstructRep]; unfold obstruct rawCut; rw [Finset.prod_eq_zero t (lit_low _ p),Complex.ofReal_zero,zero_smul]
lemma curved_cost (f:Family J){C:ℝ}(t:pay f C):pay (curved J U n f) C:=by
  intro v x; rw [obstructRep,norm_smul]; exact (mul_le_mul_of_nonneg_right (obstructPay ..) (norm_nonneg _)).trans (by rw [one_mul]; exact t v x)
lemma curve_color (f:Family J)(h: CovCover J f): CovCover J (curved J U n f):=by
  apply (covariant_parts J _ h).2; intro v g x
  let V:=obstruct U n; have e:∀ i:Fields (J.c v), scalar J V v i= V (onC _ i.1,onC _ i.2) • 1:=fun _ => rfl
  rw [e,e,Fock.twist_scalar,map_one]; apply congrArg (fun t:ℂ=> t • (1:FC _)); unfold V obstruct rawCut; apply congrArg
  have he: (simultaneous g x).1=Lattice.gauge g x.1:=rfl; simp_rw [tile_face,he,face_gauge,Gauge.chord_conj]

lemma curve_view {m N:Side}(L:J.c m=N)(x:Fields N)(f:Family J):
    Tapestry.arrange _ _ L (curved J U n f m) x=obstruct U n (onC _ x.1,onC _ x.2) • Tapestry.arrange _ _ L (f m) x:=by subst N; exact obstructRep ..
lemma aperture_on (m:Side)(t:Loom m): ∀ᵐ x:Orbit m∂city m,
   ∀ᶠ n in atTop,obstruct U n (onC m x.1,onC m (t x))=1:=by
  refine ((MeasureTheory.ae_all_iff (ι:=↑U)).mpr (fun c=> CF.Signal.Showcasing.displacement m (wrap (More m) c.val.1,c.val.2))).mono ?_
  intro x hx; have hp : ∀ᶠ n in atTop,∀ c:↑U, rawCut n c.val (onC _ x.1)=1:= eventually_all.mpr fun c=>by unfold rawCut; simp_rw [tile_face]; exact lit_keep (hx c)
  apply hp.mono; intro i hi; unfold obstruct; rw [Finset.prod_eq_one (fun c v=> hi ⟨c,v⟩), Complex.ofReal_one]

variable (s:ℕ)
local notation "T" => catalog Y H V G j strict C
lemma paysAperture (f:Family K): Dues Y H G s (fun n=> curved K U n f-f):=by
  apply Eventually.of_forall; intro u; let m:=i (G.rows u); let e:= terrain Y H (Y.ir m) s
  filter_upwards [aperture_on U (side Y m s) ((Y.voyage m).CapeT s)] with x t
  apply tendsto_const_nhds.congr'; filter_upwards [t] with n v; rw [map_sub]; change (0:FC (Single (side Y m s)))=Tapestry.arrange _ _ e (curved K U n f _) _- _
  rw [curve_view]; change _=obstruct U n (onC _ x.1,onC _ (((Y.voyage m).CapeT s) x)) • _ - _; rw [v,one_smul]; exact (sub_self _).symm -- instance

lemma higher (w:restsOn U S)(f:Family K)(h:InTest K true S false f)(n:ℕ): InTest K true S false (curved K U n f) := InTest.mul ((InTest.seed (cutC S U n w)).widen) h
variable (Ct:Arena Y H G.history.circuit j 0 false)
noncomputable def movedF (f:observable K true)(v:InTest K true S false f.val)(w:restsOn U S) : observable K true:= ⟨curved K U n f.val,aux_test (higher Y H S U w f.val v n),fun _=>curve_color K U n _ (f.property.2 rfl)⟩
local notation "q"=>seal₀ Y H V G j false Ct s
lemma settled (w:restsOn U S) (f:observable K true) (h:InTest K true S false f.val):
    Tendsto (fun n=> q (restore (movedF Y H S U n f h w))) atTop (𝓝 (q (restore f))) :=by
  obtain ⟨C,v⟩:=Journey.valuation Y H h; refine at_r Y H V G j S s Ct _ _ h (A':=C+C) (fun n=> higher Y H S U w f.val h n) (fun n m x=> ?_) (paysAperture Y H G U s f.val)
  exact (norm_sub_le ..).trans (add_le_add (curved_cost K U n _ v m x) (v m x))
open Theory
include G V Ct in
lemma prices_irr (w:restsOn U S) (f:observable K true) (h:InTest K true S false f.val):
    Tendsto (fun n=> E s (curved K U n f.val)) atTop (𝓝 (E s f.val)):=by
  let Q:= catalog Y H V G j false Ct; let A':=seat0 Y H V G.history j false Ct; let F(x:Q):=inner ℂ A' (x.val A'); let t:=settled Y H V G j S U s Ct w f h
  have he(f: observable K true):E s f.val= F (q (restore f)):= (Vacancy.inspected (F:=restore f) Y H V s G.history G.clipped j false Ct).symm
  have hp:Continuous F:=continuous_const.inner (continuous_subtype_val.clm_apply continuous_const) -- tune
  conv_rhs => rw [he f]
  exact (((hp.tendsto _).comp t).congr (fun n => (he (movedF Y H S U n f h w)).symm)) -- wrong dir & note notation binder
lemma prices_selected (w:restsOn U S)(f:observable K true)(h:InTest K true S false f.val)(x:Resident (catalog Y H V G j false Ct)):
    Tendsto (fun n=> markE Y H V G false j Ct x s (restore (movedF Y H S U n f h w))) atTop (𝓝 (markE Y H V G false j Ct x s (restore f))):= (show Continuous (eye x) from (show Resident (catalog Y H V G j false Ct) from x).val.continuous).continuousAt.tendsto.comp (settled Y H V G j S U s Ct w f h) -- name

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.prices_selected
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.prices_irr
