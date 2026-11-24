import YM.SU5.Reconstruction.Oblique.Apter
import YM.SU5.Reconstruction.FirstWindows.MovingKets
/-!
# CPI exposure. Angular Tilt purchases & D meters; Acts on whole **TEST** (CP1 target), actual θ_spin on chiral FOLK. Still need fund continuity instructions to use in Mink; even on AREA residents preservation pending diagnosis. Sources real. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
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
local notation "D" => Domain Y H G
variable (P:Ramp) {J: Calibration}
noncomputable def windTilt (P:Ramp)(J:Calibration): Dome J→ₗ⋆[ℂ]Dome J where
 toFun f:=⟨P.cuspF J f.val, aux_test (P.faces J ((marque ..).1 f.property).paid.choose_spec)⟩
 map_add' _ _:= Subtype.ext (P.over_add J)
 map_smul' c _:= Subtype.ext (P.over_z J c)
lemma twice_dome (f:Dome J): windTilt P J (windTilt P J f)=f:= Subtype.ext (P.twice_over J ((marque ..).1 f.property).paid.choose_spec)
noncomputable def gust (P:Ramp)(J:Calibration) : Sky J→ₗ⋆[ℂ] Sky J:= skySemilinear fun _=>windTilt P J
lemma gust_unit (J:Calibration): gust P J 1=1:= Filter.Germ.coe_eq.mpr (Eventually.of_forall fun _=>Subtype.ext (P.over_id J)) -- tune map mutation
lemma gust_mul (f g:Sky J): gust P J (f*g)=gust P J f*gust P J g:= sky_change_mul (fun _ f=> windTilt P J f) (Eventually.of_forall fun _ _ _=>Subtype.ext (P.over_times J)) f g
lemma gust_z(f:Sky J)(z:ℂ): gust P J (z • f)=star z • gust P J f:= (gust P J).map_smulₛₗ ..
lemma gust_square(f:Sky J): gust P J (gust P J f)=f:=by induction f using Filter.Germ.inductionOn with | _ f=> exact Filter.Germ.coe_eq.mpr (Eventually.of_forall fun n=>twice_dome P (f n))
include V in
lemma gust_ticket (s:ℕ)(f:Dome (tent Y H)): gust P K (ticket Y H G s f)=ticket Y H G s (windTilt P K f):= Filter.Germ.coe_eq.mpr (Eventually.of_forall fun t=>Subtype.ext (Tilted.every_price Y H V G P s ((marque ..).1 f.property) (t-s)).symm)
-- purchasing calibration
lemma rotates_shield {x:Cover}{p:RSpace}(s:ℕ)(u:p∈Tapestry.shield Λ l s x): P.s.act p∈ Tapestry.shield Λ l s (P.s.act x):=by
 intro i; obtain ⟨j,rfl⟩:=P.s.perm.surjective i
 unfold Tapestry.shield at * -- may pi
 rw [Signed.act_at,Signed.act_at]; cases h:P.s.flip j
 · simp only [Bool.false_eq_true,ite_false]; exact u j
 simp only [↓reduceIte,mul_neg,Int.cast_neg,neg_sub_neg] -- tune
 rw [abs_sub_comm]; exact u j
lemma matter_turn(p:RSpace): P.s.act (toMatterUnits p)=toMatterUnits (P.s.act p):=by
 funext i; obtain ⟨j,rfl⟩:=P.s.perm.surjective i; rw [Signed.act_at]; unfold toMatterUnits; rw [Signed.act_at]; cases h:P.s.flip j <;> simp <;> ring
lemma protects (s:ℕ)(q:Bool)(U:Set RSpace)(f:Dome J)(p:f∈insideAt Λ l J q U s): windTilt P J f∈ insideAt Λ l J q (P.s.act '' U) s:=by
 obtain ⟨⟨S,t,b⟩,h⟩ := (mem_insideAt _ _).1 p
 refine (mem_insideAt _ _).2 ⟨⟨_, P.faces J t, ?_⟩, fun hq=> P.keeps_color J (aux_test t) (h hq)⟩
 apply (supported_iff ..).2; rintro y v
 obtain ⟨x,c,w,h,rfl⟩:= Set.mem_iUnion₂.mp v; obtain ⟨x,g,rfl⟩:= Finset.mem_image.mp c
 rw [P.mode_motion] at h; have hp:=rotates_shield P s h; rw [P.act_act] at hp
 refine ⟨toMatterUnits (P.s.act w), (supported_iff ..).1 b (Set.mem_iUnion₂.mpr ⟨x,g,_,hp,rfl⟩),?_⟩; rw [matter_turn,P.act_act]
include V
lemma shelters {f:Sky K}{q:Bool}{U:Set RSpace}(h:f∈D q U):gust P K f∈D q (P.s.act '' U):=by obtain ⟨s,x,p,rfl⟩:=h; rw [gust_ticket Y H V]; exact ticket_mem Y H G (protects P s q U x p)
omit V
lemma moveOff {p:Signed}{x:Cover}(s:ℕ): stamps Λ s (p.act x)=p.act (stamps Λ s x):=by
 funext i; obtain ⟨j,rfl⟩:=p.perm.surjective i; rw [stamps_at, Signed.act_at,Signed.act_at,stamps_at]; cases h:p.flip j; · simp
 simp only [↓reduceIte]; apply Subtype.ext; change bell _ s _= -bell _ s (x j); simp [bell]
lemma dome_mirror (i:Axis)(f:Dome J): windTilt P J (aureole J i 0 f)=aureole J (P.s.perm i) 0 (windTilt P J f):= by
 apply Subtype.ext; change P.cuspF J (mirror J i 0 f.val)=mirror _ _ 0 _
 have ht:= P.sees J ((marque ..).1 f.property) i 0; rw [show hush (P.s.flip i) (0:ℤ)=0 by cases P.s.flip i <;> simp] at ht; exact ht
lemma gust_mirror (i:Axis)(x:Sky J):gust P J (flipMark i J x)=flipMark (P.s.perm i) J (gust P J x):=by
 induction x using Filter.Germ.inductionOn with | _ x=> exact Filter.Germ.coe_eq.mpr (Eventually.of_forall fun n=>dome_mirror P i (x n))
lemma here_zone {x:Family J}(t:TestFamily J true x)(z:Cover)(p:List Axis): P.cuspF J (cad J p z x)=cad J (p.map P.s.perm) (P.s.act z) (P.cuspF J x):=by
 induction p with
 | nil=>rfl
 | cons j p ih=>
   rw [List.map_cons,cad_step,cad_step]; unfold relocate chime
   have hx:= cad_paid J p t z
   rw [P.sees J (reflect_ok J j 0 hx), P.sees J hx, ih, Signed.act_at]; cases h:P.s.flip j <;> simp only [Bool.false_eq_true,↓reduceIte, hush_false,hush_true, neg_zero]
   congr 2
   unfold gaugeT Heat.gaugeShift; ring
lemma zone_dome (f:Dome J)(z:Cover): windTilt P J (reposition J z f)=reposition J (P.s.act z) (windTilt P J f):=by
 apply Subtype.ext; change P.cuspF J (cad J _ z f.val)=cad J ordinate _ _; let y:=windTilt P J f
 rw [here_zone P ((marque ..).1 f.property)]
 refine cad_perm J _ ?_ (x:=y.val) ((marque ..).1 y.property) (P.s.act z)
 apply (List.perm_ext_iff_of_nodup (ordinate_one.map P.s.perm.injective) ordinate_one).2; intro i; exact ⟨fun _=>ordinates _, fun _=>List.mem_map.mpr ⟨P.s.perm.symm i,ordinates _,P.s.perm.apply_symm_apply i⟩⟩
lemma zone_gust (p:placement Λ) (x:Sky (tent Y H)): gust P K (move K p x)=move K (P.s.act p) (gust P K x):= by induction x using Filter.Germ.inductionOn with
 | _ x=>
   refine Filter.Germ.coe_eq.mpr ?_
   filter_upwards [stamps_eventually p] with i ⟨q,h⟩
   change windTilt P K (reposition K (chooseStamp p i) _)=reposition K (chooseStamp (P.s.act p) i) _
   rw [chooseStamp_eq h,chooseStamp_eq ((moveOff (p:=P.s) i).trans (congrArg P.s.act h)),zone_dome]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
