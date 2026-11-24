/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.CompassRose.Loom

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open CF.Fir CF.Jill CF.Flare CF.Kea CF.Emu Lamour Lamour.Bridge
open RoseGaussian
open WakeInvestment
variable {I J K X:Type*}
section money
-- number of petals <= budget; replicate private lemma exchanges from Petals
private lemma exchange_adequate (C:I→I→ℂ)(n m:ℕ)(l:List I)(p:l.length ≤ n)(q:l.length ≤ m): exchange C n l=exchange C m l:=by
 induction n generalizing l m with
 | zero=> simp at p; rw [p]; cases m<;> rfl
 | succ n ih=>
   cases l with
   | nil=> cases m<;>rfl
   | cons i l=> cases m with
     | zero=> rw [List.length_cons] at q; omega
     | succ m=> exact slit_dep _ (fun i _=>rfl) (fun l _ k=> ih _ _ (by rw [List.length_cons] at p; omega) (by rw [List.length_cons] at q; omega))
local notation "Λ" I:max => CTag I
local notation "Γ" I:max => sIndex I
private lemma invest_concat (f:List (Ball I)→ℂ)(l m:List I) : deposits (l++m) f=deposits l (fun q=> deposits m (fun t=> f (q++t))):=by
 induction l generalizing f with|nil=>rfl|cons i l ih=> rw [List.cons_append,deposits,deposits]; exact sum_congr rfl fun i _=> ih _
private lemma invest_shift (f:List (Ball I)→ℂ)(l:List I)(a:ℂ): deposits l (fun x=>f x*a)=deposits l f * a:= (invest_sum l f (AddMonoidHom.mulRight a)).symm
private lemma invest_pre (f:List (Ball I)→ℂ)(l:List I)(a:ℂ): deposits l (fun x=>a*f x)=a*deposits l f:= (invest_sum l f (AddMonoidHom.mulLeft a)).symm
abbrev piecePrice (Z:Γ I→Γ I→ℂ)(S:Λ I→Λ I→ℂ)(l:List (Ball I)):= charge l*exchange S l.length (l.map panelColor) * runes Z (stream l)
lemma flower_calendar (f: I → J) (L:List I)(Z:Γ J→Γ J→ℂ)(S:Λ J→Λ J→ℂ)(V:Γ I→Γ I→ℂ)(T:Λ I→Λ I→ℂ)
    (hv:∀ i j,Z (f i.1,i.2) (f j.1,j.2)=V i j)(ht:∀ i j, S (f i.1,i.2) (f j.1,j.2)=T i j):
    roseMoment (L.map f) Z S=roseMoment L V T:=by
 let g(p:Ball I): Ball J:=(f p.1,p.2); let a(p:Γ I) : Γ J:=(f p.1,p.2); let b(p:Λ I):Λ J:=(f p.1,p.2)
 have he(K:List (Ball J)→ℂ): deposits (L.map f) K=deposits L (fun u=> K (u.map g)):=by
    induction L generalizing K with| nil=> rfl| cons i l ih=> rw [List.map_cons,deposits,deposits]; exact sum_congr rfl fun v _=> ih _
 change deposits (L.map f) _= deposits L _; rw [he]; apply invest_dep; intro l Hlb; clear Hlb
 change piecePrice _ _ _= _
 have h(n:ℕ)(x:List (Λ I)) : exchange S n (x.map b)=exchange T n x:=by rw [exchange_map,show (fun i j=>S (b i) (b j))=T from funext fun i=>funext (ht i)]
 have hp: stream (l.map g)= (stream l).map a:=by induction l with|nil=>rfl|cons i l ih=> rw [List.map_cons,show stream _=legs (g i) ++ stream (l.map g) from rfl,show _ = _ from ih,show stream (i::l)= legs i ++ stream l from rfl,List.map_append]; rfl -- shape
 dsimp only [roseMoment,piecePrice]
 rw [hp, show (l.map g).length=l.length from List.length_map g, rune_map V _ a _ (fun i j=>(hv i j).symm),
   show List.map panelColor (l.map g)=(l.map panelColor).map b by simp only [List.map_map]; rfl,h]; unfold charge; rw [List.map_map]; try rfl

private lemma flying_append(Z:Γ I→Γ I→ℂ)(S:Λ I→Λ I→ℂ)(L M: List (Ball I))
    (p:∀ a∈L,∀ b∈M,S (panelColor a) (panelColor b)=0)(q:∀ a∈stream L,∀ b∈stream M,Z a b=0) :
    piecePrice Z S (L++M)=piecePrice Z S L * piecePrice Z S M:=by
  unfold piecePrice; rw [show stream (L++M)=stream L++stream M from List.flatMap_append,List.map_append,List.length_append,rune_divide _ _ _ q]; unfold charge; rw [List.map_append,List.prod_append]
  have hx(k:List (Ball I)): (k.map panelColor).length=k.length:=List.length_map _
  rw [exchange_split S, exchange_adequate _ (L.length+ M.length) L.length (L.map panelColor), exchange_adequate _ (L.length+ M.length) M.length (M.map panelColor)]
  all_goals try (simp_rw [hx]; omega)
  · ring
  intro i p' j t; obtain ⟨i,v,rfl⟩:= List.mem_map.mp p'; obtain ⟨j,u,rfl⟩:= List.mem_map.mp t; exact p i v j u

lemma rose_split (Z:Γ I→Γ I→ℂ)(S:Λ I→Λ I→ℂ) (L M:List I)
    (u:∀ (i j:Γ I),i.1∈L →j.1∈M → Z i j=0)(v:∀ (i j:Λ I),i.1∈L→j.1∈M→S i j=0) :
    roseMoment (L++M) Z S=roseMoment L Z S*roseMoment M Z S:=by
 let H:=piecePrice Z S; have h(L:List (Ball I))(i:Γ I)(t:i∈stream L):i.1∈L.map Prod.fst:=by
    obtain ⟨p,u,v⟩:=List.mem_flatMap.mp t; rw [legs,List.mem_cons,List.mem_singleton] at v; rcases v with rfl|rfl <;> exact List.mem_map.mpr ⟨p,u,rfl⟩
 change deposits _ H = deposits L H * deposits M H; rw [invest_concat,←invest_shift]
 apply invest_dep; intro x hx; rw [← invest_pre]; apply invest_dep; intro y hy
 exact flying_append Z S x y (fun i p j t => v _ _ (hx ▸ List.mem_map.mpr ⟨i,p,rfl⟩) (hy ▸ List.mem_map.mpr ⟨j,t,rfl⟩)) (fun i p j t=>u _ _ (hx ▸ h x _ p) (hy ▸ h y _ t))
end money
section
-- proof of homogeneity adapted from YM/Next/RANK/Hydro & WakeInvestment/DistancePower.
open Maxwell
open scoped ContDiff
private lemma bare_hom (a b i l) (r : ℝ) (hr : 0 < r) (x : E4) (hx : x ∈ Maxwell.away) :
    bareCurl a b i l (r • x)= (r^4)⁻¹*bareCurl a b i l x := by
  have hx : x ≠ 0 := hx
  have h : r • x ≠ 0 := smul_ne_zero hr.ne' hx
  have he (i j:Axis) : Maxwell.grad i (Maxwell.grad j Green) (r • x)= (r^4)⁻¹ * Maxwell.grad i (Maxwell.grad j Green) x := by rw [second_Green h, second_Green hx]; simp only [PiLp.smul_apply,norm_smul,Real.norm_of_nonneg hr.le,smul_eq_mul]; have hv:= norm_pos_iff.mpr hx; field_simp
  unfold bareCurl; simp only [Pi.sub_apply,Bare.opp_grad hx,Bare.opp_grad h,he, mul_sub,mul_ite,mul_zero]
private lemma pencil_scale (x:Gaia) {a:ℝ}(p:0<a): Onyx.pencil x=a^3 • Onyx.pencil (a • x):=by
 have hg: gleamV (a • x)=a • gleamV x:=by
    unfold gleamV; rw [←Matrix.mul_smul,Finset.smul_sum]; apply congrArg (minA* ·); exact Finset.sum_congr rfl fun i _=> by rw [PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]; rfl
 unfold Onyx.pencil; rw [norm_smul,Real.norm_of_nonneg p.le,hg,smul_smul,smul_smul, mul_pow,mul_inv_rev]
 congr 1; field_simp
private lemma outward (G:Gaia→ℂ)(m:ℕ)(w:m≠0)(h:∀ x:Gaia,x≠0→ ContinuousAt G x)(t:∀ x:Gaia, x≠0 →∀ r:ℝ,0 < r → G x=r^m • G (r • x))(X:ℕ→Gaia) (e:Tendsto (fun i=>‖X i‖) atTop atTop) : Tendsto (fun i=>G (X i)) atTop (𝓝 0):=by
 let f(i:ℕ):= ‖X i‖; let S:=Metric.sphere (0:Gaia) 1; have hp:ContinuousOn G S:= fun x v=>(h x (fun q=>by rw [q] at v; simp [S] at v)).continuousWithinAt; obtain ⟨C,c⟩:= isCompact_sphere (0:Gaia) 1|>.exists_bound_of_continuousOn hp
 rw [tendsto_zero_iff_norm_tendsto_zero]; have he:= ((tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α:=ℝ) w).comp e)).mul_const C); rw [zero_mul] at he; apply squeeze_zero' (g:=fun i=>(f i^m)⁻¹*C) (Eventually.of_forall fun i=>norm_nonneg _) ?_ he; filter_upwards [e.eventually_gt_atTop 0] with i p; let a:=f i; let y:=a⁻¹ • X i; have h0:0<a:=p; have hv:‖y‖=1:=by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr h0).le]; exact inv_mul_cancel₀ h0.ne'
 have hr: ‖G y‖ ≤ C:= c _ (by rw [mem_sphere,dist_zero_right,hv]); rw [t y (norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)) a h0, show a • y=X i from smul_inv_smul₀ h0.ne' _, norm_smul,Real.norm_of_nonneg (pow_nonneg h0.le _)] at hr
 change ‖G (X i)‖≤ (a^m)⁻¹*C; have hx:= pow_pos h0 m; rw [mul_comm _ C, ←div_eq_mul_inv]; rw [mul_comm] at hr; exact (le_div_iff₀ hx).2 hr
-- public for Spin components arbitrary; continuity on union for later; use canon signature not arbitrary parity
lemma curl_out (F D:PlaqAxes)(X:ℕ→Gaia)(e:Tendsto (fun i=>‖X i‖) atTop atTop): Tendsto (fun i=>specter F D (X i)) atTop (𝓝 0):=by
 let A : E4 → ℝ:= Maxwell.bareCurl F.val.1 F.val.2 D.val.1 D.val.2
 apply outward (fun x=>specter F D x) 4 (by decide) ?_ ?_ X e
 · intro x v; exact Complex.continuous_ofReal.continuousAt.comp ((Maxwell.Bare.curl_diff v _ _ _ _).continuousAt)
 · intro x v r p; have he:A (r • x) = (r^4)⁻¹ * A x:= bare_hom _ _ _ _ r p x v; change ↑(A x)= (r^4:ℝ) • (A (r • x):ℂ); rw [he,Complex.real_smul]; push_cast; field_simp
lemma shot_ink (L G:DirSpin) {x:Gaia}(p:x≠0):ContinuousAt (fun x=>shotL x L G) x:=by
 have hx:ContinuousAt pencil x:=by
    refine ContinuousAt.smul (g:=gleamV) (f:=fun x:Gaia=>(Real.pi^2*‖x‖^4)⁻¹) ?_ ?_
    · exact ContinuousAt.inv₀ (f:=fun x:Gaia=> Real.pi^2*‖x‖^4) (by fun_prop) (mul_ne_zero (pow_ne_zero _ Real.pi_pos.ne') (pow_ne_zero _ (norm_pos_iff.mpr p).ne'))
    unfold gleamV; apply ContinuousAt.mul continuousAt_const; apply Continuous.continuousAt; exact continuous_finsetSum _ (fun i _=> ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ _)).smul continuous_const))
 exact (continuous_id.matrix_elem _ _).continuousAt.comp hx
lemma pole_out (L D:DirSpin)(X:ℕ→Gaia)(e:Tendsto (fun i=>‖X i‖) atTop atTop): Tendsto (fun i=>shotL (X i) L D) atTop (𝓝 0):=by
 apply outward (fun x=>shotL x L D) 3 (by decide) (fun _ x=> shot_ink L D x) ?_ X e; intro x v r p; exact congrArg (fun i:Op SpinIdx=> i (dnSpin L.2) (upSpin D.1)) (pencil_scale x p)
end

variable (F: List I)(G:List J)(x:I→Gaia)(y:J→Gaia)(U:ℕ→I→Gaia)(V:ℕ→J→Gaia)
variable (u:∀ n i j,U n i-U n j=x i-x j)(v:∀ n i j,V n i-V n j=y i-y j)(p:∀ i j,Tendsto (fun n=> dist (U n i) (V n j)) atTop atTop)
section
private def joint {δ : Type*}(C:I×δ→I×δ→ℂ)(D:J×δ→J×δ→ℂ) (i j : (I ⊕ J) × δ) : ℂ:= match i.1,j.1 with| Sum.inl a,Sum.inl b=> C (a,i.2) (b,j.2)|Sum.inr a,Sum.inr b=> D (a,i.2) (b,j.2)|_,_=>0
private lemma small_stems {X : ℕ→I→ Gaia}(d:I→DirSpin)(i j:sIndex I)(p:Tendsto (fun n=> dist (X n i.1) (X n j.1)) atTop atTop) : Tendsto (fun n=> spinRow (X n) d i j) atTop (𝓝 0):=by
 let x(n):=X n i.1; let y(n):= X n j.1; let r:= pole_out (d i.1) (d j.1) (x-y) (p.congr fun n=> dist_eq_norm ..); let t:= pole_out (d j.1) (d i.1) (y-x) (p.congr fun n=> (dist_comm ..).trans (dist_eq_norm ..)); unfold spinRow arms; split_ifs; exact tendsto_const_nhds; exact r; simpa only [Pi.sub_apply,y,x,neg_zero] using t.neg
private lemma small_gauge {X:ℕ→I→ Gaia}(d:I→PlaqAxes)(i j: CTag I)(p:Tendsto (fun n=> dist (X n i.1) (X n j.1)) atTop atTop) : Tendsto (fun n=> tideRow (X n) d i j) atTop (𝓝 0):=by
 simpa only [mul_zero] using (curl_out (d i.1) (d j.1) (fun n=> X n i.1-X n j.1) (p.congr fun n=>dist_eq_norm ..)).const_mul (↑(sch (G:=SU.group) i.2 j.2):ℂ)
-- no geometry hypothesis even if coincident! Not model price at that self argument; only the algebraic rule of bill decouples so.
include u v p
lemma rose_falling (d:I→PlaqAxes)(e:J→PlaqAxes)(g:I→DirSpin)(b:J→DirSpin) : Tendsto
    (fun n=> bill (Sum.elim (U n) (V n)) (Sum.elim d e) (Sum.elim g b) ((F.map Sum.inl)++(G.map Sum.inr))) atTop (𝓝 (bill x d g F*bill y e b G)):=by
 let X:= I ⊕ J; let S(n):X→Gaia:= Sum.elim (U n) (V n); let E:= Sum.elim d e; let D:= Sum.elim g b; let L:= (F.map (Sum.inl : I→X))++G.map Sum.inr; let ℓ(n):=spinRow (S n) D; let γ(n):=tideRow (S n) E; let T:= spinRow x g; let R:= spinRow y b; let P:= tideRow x d; let Q:= tideRow y e; let A:= joint T R; let B:= joint P Q
 have hr(i j:sIndex X): Tendsto (fun n=> ℓ n i j) atTop (𝓝 (A i j)):=by
    rcases i with ⟨a|a,f⟩ <;> rcases j with ⟨b'|b',k⟩
    · refine tendsto_const_nhds.congr fun n=>Eq.symm ?_; dsimp only [ℓ,spinRow,A,S,T,joint,D, Sum.elim_inl]; rw [u,u] -- tune
    · exact small_stems D _ _ (p _ _)
    · exact small_stems D _ _ ((p b' a).congr fun n=> dist_comm ..)
    · refine tendsto_const_nhds.congr fun n=>Eq.symm ?_; dsimp only [ℓ,spinRow,A,R,S,joint,D, Sum.elim_inr]; rw [v,v]
 have ht(i j:CTag X): Tendsto (fun n=> γ n i j) atTop (𝓝 (B i j)):=by
    rcases i with ⟨i|i,f⟩ <;> rcases j with ⟨j|j,k⟩
    · refine tendsto_const_nhds.congr fun n=>Eq.symm ?_; dsimp only [γ,tideRow,B,P,S,joint,E, Sum.elim_inl]; rw [u]
    · exact small_gauge E _ _ (p _ _)
    · exact small_gauge E _ _ ((p j i).congr fun n=> dist_comm ..)
    · refine tendsto_const_nhds.congr fun n=>Eq.symm ?_; dsimp only [γ,tideRow,B,Q,S,joint,E, Sum.elim_inr]; rw [v]
 have he:Tendsto (fun n=>roseMoment L (ℓ n) (γ n)) atTop (𝓝 (roseMoment L A B)):=by
    apply invest_limit L atTop (fun t n=>piecePrice (ℓ n) (γ n) t) _; intro t _; exact ((exchange_limit B atTop γ _ t.length (List.pairwise_of_forall (fun i j=> ht i j))).const_mul (charge t)).mul (spin_leap _ A _ hr _)
 let a:= (Sum.inl : I→X); let x':= (Sum.inr : J→X)
 have hu {Δ : Type}(t:I×Δ→I×Δ→ℂ)(q:J×Δ→J×Δ→ℂ)(i j:X×Δ) (h:i.1∈F.map a)(l:j.1∈G.map x'):joint t q i j=0:=by
    obtain ⟨b,p,hb⟩:= List.mem_map.mp h; obtain ⟨c,f,H⟩:= List.mem_map.mp l; rw [joint,← hb,←H]
 change Tendsto (fun n=> roseMoment L _ _) _ _
 rw [show roseMoment L A B= bill x d g F*bill y e b G from ?_] at he; exact he
 exact (rose_split A B (F.map a) (G.map x') (fun i j=> hu T R i j) (fun i j=> hu P Q i j)).trans (congrArg₂ (· * ·) (flower_calendar a F A B T P (fun _ _=>rfl) (fun _ _=>rfl)) (flower_calendar x' G A B R Q (fun _ _=>rfl) (fun _ _=>rfl)))
end
#print axioms rose_falling
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
