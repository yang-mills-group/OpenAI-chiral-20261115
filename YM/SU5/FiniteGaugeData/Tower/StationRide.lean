/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Tower.TimeKeeper
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Set
/-! # Drive estimate for resolution Hilbert. Dense entrants only, but
symmetry on all and reciprocated for reflected Entry; exact cost. No
assertion period-free h bound except AS Λ,Y etc supplied. -/
section pace
variable {V : Type*} [AddCommMonoid V] [Module ℂ V] {H : Hilbert}
-- From YM/OS/Train, against specializes to one vector. Entire extrapolation
-- and re-placement costs in this project done anew for resolution operators,
-- not assertions of Table applications.
private lemma driver (A B : V→ₗ[ℂ] V) (X : V →ₗ[ℂ] H) (D : ℝ) (h : 0<D)
    (hp : ∀ v w, inner ℂ (X (A v)) (X w)=inner ℂ (X v) (X (B w)))
    (v : V) (ht : ∃ C : ℝ, ∀ n:ℕ, ‖X (((B ∘ₗ A)^n) v)‖ ≤ C*D^(2*n)) :
    ‖X (A v)‖ ≤ D*‖X v‖ := by
  let T : V→ₗ[ℂ] V := B ∘ₗ A
  have hh (v w) : inner ℂ (X v) (X (T w))=inner ℂ (X (T v)) (X w) := by
    change inner ℂ (X _) (X (B _))=_
    rw [← hp,← inner_conj_symm (X (A v)),hp,inner_conj_symm];rfl
  have hw n (v w) : inner ℂ (X v) (X ((T^n) w))=inner ℂ (X ((T^n) v)) (X w) := by
    induction n generalizing v w with
    | zero => rfl
    | succ n ih =>
      conv_rhs => rw [pow_succ]
      conv_lhs => rw [pow_succ']
      rw [show (T*T^n) w=T ((T^n) w) from rfl, hh, ih];rfl
  obtain ⟨C,hC⟩ := ht
  let d n := ‖X ((T^n) v)‖/D^(2*n)
  have Ht n : 0 ≤ d n := by unfold d; positivity
  have he : BddAbove (range d) := by
    refine ⟨C, fun c he => ?_⟩; obtain ⟨i,rfl⟩ := he
    exact (div_le_iff₀ (pow_pos h _)).2 (hC _)
  let s := ⨆ i, d i
  have hr n : d n≤ s := le_ciSup he _
  have hz n : d n ^ 2 ≤ ‖X v‖ * s := by
    have hi : ‖inner ℂ (X v) (X ((T^(n+n)) v))‖= ‖X ((T^n) v)‖^2 := by
      rw [pow_add,Module.End.mul_apply, hw,inner_self_eq_norm_sq_to_K]; simp
    calc _ = ‖inner ℂ (X v) (X ((T^(n+n)) v))‖/D^(2*(n+n)) := by unfold d; rw [hi,div_pow, Nat.mul_add, pow_add, pow_two (D^_)]
         _ ≤ ‖X v‖*d (n+n) := by
             apply (div_le_div_of_nonneg_right (norm_inner_le_norm _ _) (pow_nonneg h.le _)).trans (le_of_eq ?_); unfold d; ring
         _ ≤ _ := by gcongr; exact hr _
  have hs := (Ht 0).trans (hr 0)
  have hu : s ≤ ‖X v‖ := by
    have hx : s ≤ √(‖X v‖*s) := ciSup_le fun i => (Real.le_sqrt (Ht i) (by positivity)).mpr (hz i)
    have he := Real.sq_sqrt (show 0 ≤ ‖X v‖*s by positivity)
    nlinarith [norm_nonneg (X v)]
  have hy : ‖X (A v)‖^2=‖inner ℂ (X v) (X ((T^1) v))‖ := by rw [pow_one,show X (T v)=X (B (A v)) from rfl,← hp];simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  rw [hy]
  have hr : ‖X ((T^1) v)‖ ≤ ‖X v‖*D^(2*1) := (div_le_iff₀ (pow_pos h _)).1 ((hr 1).trans hu)
  apply (norm_inner_le_norm _ _).trans
  exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans_eq (by ring)
end pace
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(strict:Bool)
variable (C:Arena Y H Q.circuit j 0 strict) -- tune
variable (w:ℕ)(f:Entry Y H s j strict w)
variable (Qt : Clipped Y H (i∘a) (k∘b))(hw:0 < w)
local notation "A"=> Ark.Ht Y H Q.circuit j 0 strict C
local notation "Γ" i:max=> Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s Q.circuit j 0 strict C

include V C
lemma excursion (u:Γ s) (n:ℕ):
 let x:=slabT Y H s j strict w f
 let y:=slabT Y H s j strict w (inverse Y H s j strict w f)
 ‖(κ s) (((y ∘ₗ x)^n) u)‖^2 = ‖E s (chambers j w (0:ℤ) f.val.val u.val (2*n))‖:=by
 intro x y
 let z:= (lace (tent Y H) j (↑w:ℤ) f.val.val u.val (2*n))
 have hi(t : Γ s): ‖(κ s) t‖^2= ‖E s (mirror K j 0 t.val * t.val)‖:=by
    have hv:inner ℂ ((κ s) t) ((κ s) t)=E s (mirror K j 0 t.val*t.val):=by rw [stems Y H V Q.circuit,area0]
    rw [←hv,inner_self_eq_norm_sq_to_K,norm_pow]; change _= ‖((‖(κ s) t‖:ℝ):ℂ)‖^2; simp

 have he(r:ℕ):(((y ∘ₗ x)^r) u).val =lace (tent Y H) j w f.val.val u.val (2*r):=by
    induction r with
    | zero=> rfl
    | succ r ih=>
       rw [pow_succ',Module.End.mul_apply,LinearMap.comp_apply]
       unfold x y; rw [slab_eq,slab_eq]; unfold x y at ih; rw [ih, overlay K j _ _ _ (test_entry Y H s j strict f) r]; rfl -- repeat issue
 let t:=test_entry Y H s j strict f; let k:= (exam j _ K ((purpose_ok ..).mp u.property).1).1; let p:=lace_paid K j (w:ℤ) t k (2*n)
 rw [hi,he]
 unfold chambers; rw [relocate_zero K j ((reflect_ok K j _ p).mul p)]

-- registration term in slot at higher resolution
noncomputable def furnished(t:ℕ)(h:s ≤ t): Entry Y H t j strict (Λ.R.L.val^(t-s)*w):=by
 let e:=Λ.R.L.val^(t-s)
 let v:= Raise Y H Q.circuit j 0 strict s t h f.val
 let S:=f.property.choose; let a:=f.property.choose_spec.1; let eH:=f.property.choose_spec.2
 let dS:=volumeAround Λ l (t-s) S
 have ht:Between K j (0:ℤ) (ruler Λ.block*(e*w:ℕ)) dS:=by unfold e; rw [Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact expands_shape Y H eH _
 exact ⟨v,dS,(proceeds Y H Q.circuit s (t-s) a).1,ht⟩

local notation "T" i:max h:max=>furnished Y H s Q j strict w f i h
include Q
lemma launch(t r:ℕ)(p:s ≤ t)(q:t ≤ r):
 (T r (le_trans p q)).val=Raise Y H Q.circuit j 0 strict t r q ((T t p).val):=by
 apply Subtype.ext
 have he:=congrArg Subtype.val (linking_diagram Y H Q.circuit j 0 p q (freeze Y H s j 0 strict f.val)); exact he.symm
lemma reverse_launch (t:ℕ)(p:s ≤ t):
 furnished Y H s Q j strict w (inverse Y H s j strict w f) t p=inverse Y H t j strict (Λ.R.L.val^(t-s)*w) (T t p):=by
 apply Subtype.ext; apply Subtype.ext
 let c:=t-s; let L:=Λ.R.L.val
 change stream Y H D s c (mirror K j (gaugeT K (w:ℤ)) f.val.val)=mirror _ _ _ (stream Y H D s c f.val.val)
 rw [stream_flipped Y H Q.circuit s c j _ (test_entry ..)]
 -- unfold s exact
 congr 1; unfold gaugeT Heat.gaugeShift; push_cast; ring

-- detached seam qualification on the cover (any temporal only)
omit V C Q
lemma cover_between (Z:Calibration)(Λ':Preparation)(l':ℕ)(h:Z.ℓ=Journey.reserve Λ' l')(j:Axis){m₀:ℤ}{S M:Finset Cover}
 (p:∀ i∈S,i j+Z.ℓ ≤ m₀)(q:Tower.region j m₀ Z.ℓ M): Detached Λ' l' S M:=by
 intro i e x a b
 have hc:=Lattice.box_test.mp b |>.1 j; specialize p i e; specialize q x a; simp only [Pi.sub_apply,h] at *; have hf:=margin_good Λ' l'; omega
include V C Q
-- comp through resolution
lemma along (t r:ℕ)(p:s ≤ t)(q:t ≤ r)(x: Γ t):
 let B t:= Λ.R.L.val^(t-s)*w
 Raise Y H Q.circuit j 0 strict t r q (slabT Y H t j strict (B t) (T t p) x)=slabT Y H r j strict (B r) (T r (le_trans p q)) (Raise Y H Q.circuit j 0 strict t r q x):=by
 intro B
 let F:=(T t p).val; let S:= (T t p).property.choose; obtain ⟨a,h⟩:= (show InTest K true S false F.val ∧ Between K j 0 (ruler Λ.block*(B t)) S from (T t p).property.choose_spec)
 let u:=relocate K j (B t)
 obtain ⟨A₀,e,v⟩:=(show ∃ M:Finset Cover,InTest K true M false x.val∧Tower.region j (meshface (Λ:=Λ) 0 t) (K).ℓ M from ((purpose_ok ..).mp x.property).1)
 let d:=ruler Λ.block*(↑(B t):ℤ)
 let G:=plow K j (B t) A₀; have hg:Tower.region j d (K).ℓ G:=by
    intro i z; obtain ⟨i,z₀,rfl⟩:=plow_stays K j _ _ z; rw [moves,if_pos rfl]; specialize v i z₀; rw [area0] at v; change _ ≤ i j+d; linarith
 have hu:=flow_port K j (gaugeT K (B t)) e
 have hd':=(cover_between K Λ l rfl j (S:=S) (fun i v=>(h i v).2) hg)
 apply Subtype.ext
 change stream Y H D t (r-t) (slabT Y H t j strict _ _ x).val=_
 rw [slab_eq, slab_eq, launch Y H V s Q j strict C w f t r p q]
 let H':=stream Y H D t (r-t)
 change H' (F.val*u x.val) = H' F.val * relocate K j (B r) (H' x.val)
 unfold H' u relocate
 rw [woven_product Y H Q.circuit t (r-t) a hu hd'] -- tune name, argument
 unfold gaugeT
 rw [show (K).B=Λ.block from rfl, chime_X Y H V t j (2*(↑(B t):ℤ)) Q.circuit (aux_test e)]
 have ht:L₀^(r-t)*B t=B r:=by unfold B; rw [←mul_assoc,←pow_add,show r-t+(t-s)=r-s by omega]
 congr 3
 rw [←ht, Nat.cast_mul,Nat.cast_pow]; unfold B; push_cast; ring


local notation "uM" t:max=> (L₀^t*w)
local notation "M" i:max x:max=>slabT Y H i j strict (Λ.R.L.val^(i-s)*w) x
lemma horizontal_time(t:ℕ)(p:s≤ t)(x:Γ t):
 let b:= 3*w
 let v:=advance Y H V Q.circuit j 0 strict C (MeshClock.whenly (timeMesh Λ) s b) -- define
 v ((κ t) x)= (κ t) (tick Y H t j 0 strict (2*(L₀^(t-s)*b)) x):=by
 intro b v; unfold v; rw [advance_at,limited_time Y H V _ Q.circuit j 0 strict C _ p,amount,show L₀^(t-s)*(2*b)= 2*(L₀^(t-s)*b) from by ring]

local notation "KTT" i:max t:max=>tick Y H t j 0 strict i
include Qt hw
lemma drives_paid:∃B:ℝ,0<B∧ ∀ t:ℕ,∀ p:s ≤ t,∀x:Γ t,
 let y:Γ t := (KTT (2*(L₀^(t-s)*(3*w))) t) x
 ‖(κ t) ((M t (T t p)) y)‖ ≤ B*‖(κ t) y‖:=by
 obtain ⟨S,h⟩:= f.property; have hp:= test_entry Y H s j strict f
 obtain ⟨B,b,hB⟩:=baggageH Y H V s Q j w f.val.val S h.1 h.2 Qt hw
 let q:=Real.sqrt B
 have HQ:0<q:=Real.sqrt_pos.mpr b
 refine ⟨q,HQ,?_⟩
 intro t p x y
 let r:= t-s; let e:=L₀^r; let d:=e*w
 let z:=T t p; let q':=inverse Y H t j strict d z
 let Y₁:= M t (T t p)
 let Z₁:= M t q'
 let F:=arrows Y H V Q.circuit j 0 strict C t
 refine driver (H:=A) Y₁ Z₁ F q HQ (fun i b=>symmetry Y H V _ Q.circuit j strict C z i b) y ?_
 obtain ⟨A₀,m₀,g⟩:= (show ∃ KTT':Finset Cover,InTest K true KTT' false x.val∧ Tower.region j (meshface (Λ:=Λ) 0 t) (K).ℓ KTT' from ((purpose_ok ..).mp x.property).1)
 let v:= (3*d:ℕ); let W:= plow K j (v:ℕ) A₀
 have hv': y.val=relocate K j (v:ℤ) x.val:=by
    change chime K j (Heat.gaugeShift Λ.block _) _=chime _ _ (gaugeT K _) _
    unfold v d e r gaugeT; push_cast; rw [show (K).B = Λ.block from rfl]; congr 2; ring
 have hv:InTest K true W false y.val:= hv'.symm ▸ (flow_port K j _ m₀)
 let i:= ruler Λ.block*d
 have Hl:∀I∈ W, 2*i+(K).ℓ ≤ I j:=by
    intro u v'; obtain ⟨m',t',rfl⟩:= plow_stays K j (v:ℕ) A₀ v'; specialize g m' t'; rw [moves,if_pos rfl]; rw [area0] at g
    unfold v i; change _ ≤ _+ruler Λ.block*(↑(3*d:ℕ):ℤ)
    have h':0 ≤ ruler Λ.block:=(ruler_gene _).le; push_cast; nlinarith
 obtain ⟨Δ,k⟩:=Tower.sizes W; obtain ⟨i',ht⟩:= k j
 let c:ℤ:= |i'|+Δ+(K).ℓ; have hd:0≤c:=by unfold c; positivity
 have he:Between K j (2*i) c W:=by intro z v; unfold c; have h:=ht z v; exact ⟨Hl z v,by linarith [le_abs_self i']⟩
 obtain ⟨a,qx⟩:=Journey.valuation Y H hv
 let a':=a+1; have hx:0<a':= by unfold a'; exact add_pos_of_nonneg_of_pos (pay_nonneg (F:=y.val) qx) one_pos
 have ht:pay y.val a':=fun i x=> le_trans (qx ..) (by unfold a'; linarith)
 let J:=wages K (duetCharge Y (s+r)) Δ c a'; have hJ:0≤J:=by unfold J wages closefare; positivity
 refine ⟨Real.sqrt J,fun n=>?_⟩
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
 rw [mul_pow, Real.sq_sqrt hJ, ← pow_mul q,show 2*n*2=2*(2*n) from by ring, pow_mul q 2, show q^2=B from Real.sq_sqrt b.le]
 -- packaged excursion
 change ‖(κ t) (((slabT Y H t j strict _ _ ∘ₗ slabT Y H t j strict _ _)^n) y)‖^2≤ _
 rw [excursion Y H V t Q j strict C d z y n]
 have hp:=hB r Δ W c hd y.val hv (by simpa only [i,d,e,Nat.cast_mul,Nat.cast_pow] using he) k a' hx ht (2*n)
 let F':= chambers j ((e*w:ℕ):ℤ) 0 (stream Y H D s r f.val.val) y.val (2*n)
 change ‖E t F'‖ ≤ _
 unfold F'; rw [show ((e*w:ℕ):ℤ) = (L₀:ℤ)^r*w from by unfold e; push_cast; rfl]; have hh:s+r=t:=Nat.add_sub_of_le p; generalize stream Y H D s r f.val.val=a at hp ⊢; rw [hh] at hp; unfold J; rw [hh]; exact hp
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.drives_paid
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.along
