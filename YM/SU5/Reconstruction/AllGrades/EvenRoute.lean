import YM.SU5.Reconstruction.AllGrades.Sparks
import YM.SU5.Reconstruction.Nymph.Pinnacle
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Fm"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open WindRose PolarArchives ConePrice SelectionAnalysis Chambers Brazier
variable (C:∀ j, Arena Y H G.history.circuit j 0 false)(j:Axis)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "mK"=> marks (timeMesh Λ)
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped a false (C a)
local notation "Ω₀"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped a false (C a)
local notation "F₊"=> Domain Y H G false (flank a 0)
local notation "Sm" m:max=> strip a (-(m:ℝ)) (m:ℝ)
local notation "Qt" m:max=> flank a (m:ℝ)
local notation "bM" d:max=> strip a (-d) d
local notation "A₀"=> atlasAt Y H V G
local notation "Pt" m:max=> Pub Y H a m
local notation "Bk" d:max f:max => (((badge Y H V G D a b d (atlasAt Y H V G)) f))
local notation "Px" u:max f:max=> ticket Y H G u f
local notation "rF"=> studio (tent Y H) a 0 b
local notation "rW"=> studio (tent Y H) a 0 false
local notation "Δ"=> timeMesh Λ
local notation "Wq" n:max=> walkC Y H a b n
local notation "Tr"=> cruise Y H a b

/-! # Unconditional even Spacebody voter equivalence & movement. -/
open Nymph
local notation "SJ"=> displacement Y H V G.history G.clipped j false (C j) χ a (C a)
local notation "KJ"=> indoor Y H V G.history G.clipped a false (C a) SJ
local notation "Τ"=> voterAt Y H V G C j χ
local notation "Q" t:max => badge Y H V G D a false t Τ
local notation "B⚬" t:max x:max=> bud Y H V t G.history G.clipped a false (C a) SJ x
local notation "FA"=>studio (tent Y H) a 0 false
local notation "FW" t:max=> Tower.Field Y H t a 0 false
local notation "ρ" t:max u:max p:max x:max=> homePlane Y H V G D a false t u p x
local notation "Sx"=> Works Y H V G D a false Τ
noncomputable def presentAt (t:ℕ)(p:FA): FW t:=by
    refine ⟨p.val,(purpose_ok ..).2 ⟨(show (p.val) ∈ wing K a _ from ?_),nofun⟩⟩; obtain ⟨S,p₀,u⟩:=atSouth Y H a false p; rw [area0]; exact ⟨S,p₀,u⟩ -- obtain in noncomputable via classical choose (elim into Type not prop). fix
lemma present_val(t:ℕ)(p:FA): (presentAt Y H a t p).val=p.val:=rfl
lemma invitationFull(t:ℕ):Function.Surjective (presentAt Y H a t):=by
 intro x
 obtain ⟨S,q,h⟩:= (((purpose_ok ..).1 x.property).1 : ∃ S, InTest K true S false x.val ∧ Tower.region a _ _ S); rw [area0] at h
 let y:FA:=⟨x.val,S,q,h⟩; exact ⟨y, Subtype.ext rfl⟩
noncomputable def evenVac:FA:=⟨1,∅,InTest.one,by simp [Tower.region]⟩
lemma radio (p:FA) (t:ℕ)(x:FA): inner ℂ ((Q t) x) ((Q t) p)= inner ℂ (B⚬ t (presentAt Y H a t x)) (B⚬ t (presentAt Y H a t p)):=by
 rw [measures_here]; rw [Selected.earns]
 let f:Dome (tent Y H):=⟨poleForm K a 0 false x.val p.val, printedS Y H a false x p⟩
 change price Y H V G C j χ _ false f.val= _; rw [← price_across Y H V G C j χ t a ((printedS Y H a false x p).paid.choose_spec), price_oneAt Y H V G C a SJ t f]; have ht:f.val=mirror K a 0 x.val*p.val:= by change Reflect.chord _ • _=_; rw [show Reflect.chord false=1 from rfl,one_smul]
 change response Y H V t G.history G.clipped a false (C a) SJ (asLoose K f) =response Y H V t G.history G.clipped a false (C a) SJ _; exact congrArg _ (Subtype.ext ht)
lemma copy_budget {t u:ℕ}(v:t≤u)(x:FA): B⚬ u (presentAt Y H a u (ρ t u v x))=B⚬ t (presentAt Y H a t x):=by
 let F:=presentAt Y H a t x; rw [show presentAt Y H a u _ = Raise Y H G.history.circuit a 0 false t u v F from Subtype.ext rfl]; exact flourishes ..
lemma birth_equiv :∃ U:Sx≃ₗᵢ[ℂ] KJ,∀ t:ℕ,∀ x:FA,U ((Q t) x)=B⚬ t (presentAt Y H a t x):=by
 let f(x:ℕ × FA): Sx := (Q x.1) x.2; let g(x:ℕ× FA): KJ := B⚬ x.1 (presentAt Y H a x.1 x.2)
 have h₁:DenseRange f:=by
    apply (badges_roll Y H V G D a false 0 Τ).mono; intro v h; obtain ⟨i,z⟩:= Set.mem_iUnion.mp h; obtain ⟨x,rfl⟩:=z; exact ⟨(i+0,x),rfl⟩
 have h₂:DenseRange g:=by
    apply (stroll_dense Y H V G.history G.clipped a false (C a) SJ).mono; intro v h; obtain ⟨i,h⟩:= Set.mem_iUnion.mp h; obtain ⟨x,rfl⟩:=h; obtain ⟨u,rfl⟩:= invitationFull Y H a i x; exact ⟨(i,u),rfl⟩
 have h₃:∀ i j',inner ℂ (f i) (f j')=inner ℂ (g i) (g j'):=by
    intro i j'; let t:=max i.1 j'.1; let h:i.1≤t:= le_max_left ..; let ht:j'.1≤t:= le_max_right ..
    unfold f g; rw [badges_join Y H V G D a false Τ h,badges_join Y H V G D a false Τ ht, ← copy_budget Y H V G D a C j χ h, ← copy_budget Y H V G D a C j χ ht]; exact radio ..
 obtain ⟨U,p⟩ := Selected.gram_impl (A:=Works Y H V G D a false Τ) (B:=indoor Y H V G.history G.clipped a false (C a) SJ) (f:=f) (g:=g) h₁ h₂ h₃
 exact ⟨U,fun i x=> p (i,x)⟩
noncomputable def echoV:Sx≃ₗᵢ[ℂ] KJ:=(birth_equiv Y H V G D a C j χ).choose
local notation "u₀"=> echoV Y H V G D a C j χ
noncomputable def indoorK(s:ℕ)(x:FA):KJ:=B⚬ s (presentAt Y H a s x)
lemma echo_at (x:FA) : u₀ ((Q s) x)= B⚬ s (presentAt Y H a s x):= (birth_equiv Y H V G D a C j χ).choose_spec s x
local notation "Y₀"=> indoorK Y H V G a C j χ
noncomputable def nowTick (x:FA) : Domain Y H G false (flank a 0):= enclose Y H G (flank a 0) false s (fromField Y H a s (presentAt Y H a s x))
local notation "da"=> dainty Λ
local notation "tK"=> nowTick Y H G a s
lemma tick_here (x:FA):OSvector Y H V G a (C a) SJ (tK x)=B⚬ s (presentAt Y H a s x):=by unfold nowTick; rw [OSvector_enclose,as_fromField]
lemma tick_move (k:Axis)(z:ℤ)(w:a=k→ 0 ≤ 2*z)(x:FA): (tK (cart Y H a false k (2*z) w x)).val= Nymph.stride K k (notch da s z) (tK x).val:=by
 let Z:= cart Y H a false k (2*z) w x; let F(t:FA):= fromField Y H a s (presentAt Y H a s t)
 change ticket Y H G s (F Z).val= stride K k (notch da s z) (ticket Y H G s (F x).val); rw [stride_mark Y H G _ _ s z rfl]; exact congrArg _ (Subtype.ext rfl)
local notation "η"=> voter_credit Y H V G D a false C j χ
local notation "R"=> wheelTimes Y H V G D a false Τ η
local notation "χ₀"=> ride Y H V G.history G.clipped a false (C a) SJ
noncomputable def spokesman := (echoV Y H V G D a C j χ).toLinearIsometry.toContinuousLinearMap
local notation "λy"=> spokesman Y H V G D a C j χ
lemma echo_heatN (n:ℕ): (λy).comp ((R).E (whenly da s n))= ((χ₀).E (whenly da s n)).comp λy:=by
 apply badges_ext Y H V G D a false s Τ; intro i v x; let g:= MeshClock.acts da s i n; let t:= whenly da i g; let z:= notch da i (g:ℤ); rw [←MeshClock.matchR _ _ _ n v]; change (u₀) ((R).E t ((Q i) x))= (χ₀).E t (u₀ ((Q i) x))
 let v₁: FA:=walkC Y H a false g x
 rw [ages_pose, echo_at,echo_at,← tick_here Y H V G a i C j χ (x:=x)] -- order
 have he:z.val=(t:ℝ):=natural_time ..; rw [show t = Real.toNNReal z.val from (by rw [he,Real.toNNReal_coe]),time_even Y H V G j C χ a z (he.symm ▸ t.property),← tick_here Y H V G a i C j χ (x:=v₁)]
 exact congrArg _ (Subtype.ext (tick_move Y H G a i a g (by intros; positivity) x))
lemma echo_spacN(k:Trans a)(d:ℤ): (λy).comp (jolt Y H V G D a false s Τ k d)=(((outfit Y H V G j C χ a).crew k).play (notch da s d)).comp λy:=by
 apply badges_ext Y H V G D a false s Τ; intro i v x; let a':= castor da s i d; let Z:= notch da i a'; let x':= turnLane Y H a false k a' x
 change u₀ (jolt Y H V G D a false s Τ k d ((Q i) x))= ((outfit Y H V G j C χ a).crew k).play _ (u₀ ((Q i) x))
 rw [atTopLane Y H V G D a false s Τ _ _ i v,echo_at,echo_at,← notch_up da s i v,← tick_here Y H V G a i C j χ (x:=x),← tick_here Y H V G a i C j χ (x:=x'),owns_play]
 exact congrArg _ (Subtype.ext (tick_move Y H G a i k.val a' (fun h=>False.elim (k.property h.symm)) x)) -- parse orientation

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.echo_at
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.echo_heatN
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.echo_spacN
