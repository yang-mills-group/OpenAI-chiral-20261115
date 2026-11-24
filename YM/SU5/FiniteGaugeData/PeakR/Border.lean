import YM.SU5.FiniteGaugeData.PeakR.Rose
import YM.SU5.FiniteGaugeData.Mist.Ladder
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T₁: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Mist
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
namespace OutK
open KernelP Hike
open Quest.Corners
open scoped NNReal ENNReal
-- Moler: across ALL projections named in ls. any y x at horizon same s arbitrary if left neg & right pos with ahead. Ahead.Canonic.Witness only projections. Prove insertion identity. 
abbrev Largess(B:List Axis) (x y:D):= ∀ i∈B, i ≠ a→ Canaan Y h i (fire Kₜ i 0 (fire Kₜ a 0 x.val)) 0 ∧ Canaan Y h i y.val (tic Kₜ:ℤ)
local notation "E₃"=> escalant Y h W' R a s n
local notation "Θ"=> H.leaf s
local notation "C"=> ascended Y h s W' R n
local notation "V"=> Charm.W Kₜ
variable (B:List Axis)
-- general helpers
lemma heat_light (f: W (tent Y h)) (q:Canaan Y h a f (tic (tent Y h):ℤ)): Canaan Y h a (clockW Kₜ a (-1) f) 0 := by
 let Vl:= Canaan.flight Y h a f (-1) q; exact Canaan.subh Y h a _ (by simp) Vl -- notation issue
lemma aheadL' {x:W Kₜ}{b:ℤ}(p:Canaan Y h a x b)(t:0≤b): Canaan Y h a (ascended Y h s W' R n x) b := by
 induction n with
 | zero=> exact p
 | succ n ih=> exact Canaan.subh Y h a _ (by omega : b ≤ b+1) (Canaan.next Y h (s+n) W' R a _ t ih)
lemma cold_asc (f:W Kₜ) : ascended Y h s W' R n (fire Kₜ a 0 f)= fire Kₜ a 0 ((C) f):=by
 induction n with
 | zero=>rfl
 | succ n ih=> rw [ascended,LinearMap.comp_apply,ih]; change Charm.next Y h (s+n) W' R _= _; rw [next_mir,mul_zero]; rfl
lemma escalant_v : (escalant Y h W' R a s n x).val=ascended Y h s W' R n x.val:=by induction n with
 | zero=>rfl
 | succ n ih=> apply congrArg (Charm.next Y h (s+n) W' R); exact ih
lemma preferable (p:Largess Y h a B x y): Largess Y h a B (escalant Y h W' R a s n x) (escalant Y h W' R a s n y):=by
 intro i t v; rw [escalant_v,escalant_v,←cold_asc,←cold_asc]; obtain ⟨q,w⟩:=p i t v; exact ⟨aheadL' Y h s W' R i n q le_rfl,aheadL' Y h s W' R i n w (Nat.cast_nonneg _)⟩
lemma paving {b:Axis}(w:b∉B)(η:b=a→0≤z)(p:Largess Y h a B x y): Largess Y h a B x (hoist Y h a b z η y):= by
 intro i t v; obtain ⟨q,u⟩:= p i t v; exact ⟨q,Canaan.over Y h i b y.val z u (fun z=> w (z.symm ▸ t))⟩
-- fix left negative along b, promote shifts. continuum continuity
variable (X: Engine Y h W' R a H) (V':∀ a:Axis,Harbor Y h W' R Φ a)(T:∀ a:Axis,Engine Y h W' R a (V' a))
local notation "P"=> spinT Λ.R.L s 1
local notation "R₁"=> ramble X.val
local notation "L"=> Λ.R.L
-- promotion identification.Rooms.B
variable (b:Axis)(p:b ≠ a)
include X p
lemma blast : ramble X.val b (ticQ Λ.R.L s z) (H.leaf s x)= H.leaf s (hoist Y h a b z (fun i=>(p i).elim) x):=by rw [ramble_eq _ _ _ p,Driver_eq]; exact X.property ..
private lemma wick (f g: D) (x' y':Decko Y h b)(i:ℤ)(t:0 ≤ i) -- b-view motions from start
  (e:fire Kₜ a 0 f.val=fire Kₜ b 0 x'.val)(v:clockW Kₜ b z g.val=clockW Kₜ b i y'.val):
 inner ℂ (H.leaf s f) (ramble X.val b (ticQ Λ.R.L s z) (H.leaf s g)) = inner ℂ ((V' b).leaf s x') ((T b).val.stepT s b i (fun _=>t) ((V' b).leaf s y')):= by rw [blast Y h s W' R a z H _ X b p, (T b).property,H.measure, (V' b).measure]; unfold helve; rw [hoist_val,hoist_val,e,v]
variable (ℓ:Canaan Y h b (fire (tent Y h) b 0 (fire (tent Y h) a 0 x.val)) 0) (u':Canaan Y h b y.val (Chrono.tic (tent Y h) : ℤ))
local notation "u₁" => (⟨_,ℓ⟩:Decko Y h b)
local notation "v₁" => (⟨_,heat_light Y h b _ u'⟩:Decko Y h b)
include S'
-- regular_time convection
private lemma plague (t:ℤ)(H':0≤ spinT Λ.R.L s 1 + spinT Λ.R.L (s+n) t)(z:0≤(Λ.R.L.val:ℤ)^n+t) : regular Y h W' R b (V' b) (T b) (spinT L s 1+spinT L (s+n) t).toNNReal=(T b).val.stepT (s+n) b ((Λ.R.L.val:ℤ)^n+t) (fun _=>z):=by
 let v:= (Λ.R.L.val:ℤ)^n; have hQ: spinT L s 1+spinT L (s+n) t=spinT L (s+n) (v+t):=by rw [slot_add,show v= (Λ.R.L.val:ℤ)^n*1 from (mul_one ..).symm,slot_more]
 change 0≤v+t at z; obtain ⟨m,hm⟩:= Int.eq_ofNat_of_zero_le z
 rw [hQ]
 nth_rw 1 [hm]; rw [← trackT Λ,Real.toNNReal_coe,atemporal Y h (s+n) W' R A S' b (V' b) (T b) m]
 have he {J K:ℤ}(h:J=K)(t: Allows b b J)(u: Allows b b K): (T b).val.stepT (s+n) b J t=(T b).val.stepT (s+n) b K u:=by subst K; rfl
 apply he hm.symm -- `hm` may rewrite both sides dependent.Rwon`t
omit S' X p in
private lemma clock_nat (v₀ : Decko Y h b)(hv:v₀.val=clockW Kₜ b (-1) y.val)(t:ℤ) : clockW Kₜ b t (E₃ y).val=clockW Kₜ b ((Λ.R.L.val:ℤ)^n+t) (escalant Y h W' R b s n v₀).val:=by rw [escalant_v,escalant_v,hv,grow_clock,clock_add, mul_neg,mul_one]; refine congrArg (fun i=>clockW Kₜ b i _) ?_; omega
omit S' X p in
private lemma can_cold (v₀: Decko Y h b)(hv:v₀.val=fire Kₜ b 0 (fire Kₜ a 0 x.val)) : fire Kₜ a 0 (E₃ x).val=fire Kₜ b 0 (escalant Y h W' R b s n v₀).val:=by rw [escalant_v,escalant_v,hv,←cold_asc,←cold_asc,burning_ice]
section
variable (x₀ y₀:Decko Y h b)(ℓ₀:x₀.val=fire (tent Y h) b 0 (fire (tent Y h) a 0 x.val))(μ:y₀.val=clockW (tent Y h) b (-1) y.val)
include x y ℓ₀ μ
omit S' in 
private lemma sprL (t:ℤ)(z:ℤ)(hz:0≤z)(he:z=(Λ.R.L.val:ℤ)^n+t):inner ℂ (Θ x) (ramble X.val b (ticQ Λ.R.L (s+n) t) (Θ y)) = inner ℂ ((V' b).leaf s x₀) ((T b).val.stepT (s+n) b z (fun _=>hz) ((V' b).leaf s y₀)):=by
 subst z
 have Qx:= wick Y h (s+n) W' R a t H X V' T b p (E₃ x) (E₃ y) (escalant Y h W' R b s n x₀) (escalant Y h W' R b s n y₀) ((Λ.R.L.val:ℤ)^n+t) hz (can_cold Y h s W' R a n x b x₀ ℓ₀) (clock_nat Y h s W' R a n y b y₀ μ t)
 let J:=ramble X.val b (ticQ Λ.R.L (s+n) t)
 let Z:=(T b).val.stepT (s+n) b ((Λ.R.L.val:ℤ)^n+t) (fun _=>hz)
 let L' (u v:H.space):= inner ℂ u (J v); let S(u v:(V' b).space):=inner ℂ u (Z v)
 exact (congrArg₂ L' (escalate Y h s W' R a n H x).symm (escalate Y h s W' R a n H y).symm).trans (Qx.trans (congrArg₂ S (escalate Y h s W' R b n (V' b) x₀) (escalate Y h s W' R b n (V' b) y₀)))
set_option maxHeartbeats 260000 in
private lemma nourish (t: ℤ)(ht:0≤ spinT Λ.R.L s 1 + spinT Λ.R.L (s+n) t) : inner ℂ (Θ x) (ramble X.val b (ticQ Λ.R.L (s+n) t) (Θ y)) = inner ℂ ((V' b).leaf s x₀) (regular Y h W' R b (V' b) (T b) (spinT Λ.R.L s 1+spinT Λ.R.L (s+n) t).toNNReal ((V' b).leaf s y₀)):=by
 let v:= (Λ.R.L.val:ℤ)^n; have hQ: spinT L s 1+spinT L (s+n) t=spinT L (s+n) (v+t):=by rw [slot_add,show v= (Λ.R.L.val:ℤ)^n*1 from (mul_one ..).symm,slot_more]; -- tune
 have hz:= (slot_lower _ _ _).1 (hQ ▸ ht : 0≤ spinT L (s+n) (v+t))
 rw [plague Y h s W' R A S' a n H X V' T b p t ht hz]; exact sprL Y h s W' R a n H x y X V' T b p x₀ y₀ ℓ₀ μ t _ hz rfl
lemma light (t:VistaQ Λ.R.L)(ht:0≤ spinT Λ.R.L s 1+t.val): inner ℂ (H.leaf s x) (ramble X.val b t (H.leaf s y)) = inner ℂ ((V' b).leaf s x₀) (regular Y h W' R b (V' b) (T b) (spinT L s 1+t.val).toNNReal ((V' b).leaf s y₀)):= by
 obtain ⟨n,he,i,rfl⟩:= ((eventually_ge_atTop s).and (frequentT _ t)).exists; obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le he; exact nourish Y h s W' R A S' a j H x y X V' T b p x₀ y₀ ℓ₀ μ i ht
include V' T x₀ y₀ ℓ₀ μ
lemma glow : Tendsto (fun t:VistaQ Λ.R.L=> inner ℂ (H.leaf s x) (ramble X.val b t (H.leaf s y))) (𝓝 0) (𝓝 (inner ℂ (H.leaf s x) (H.leaf s y))):= by
 let l (t:VistaQ L):= spinT L s 1+t.val; let f(t:VistaQ L):=inner ℂ ((V' b).leaf s x₀) (regular Y h W' R b (V' b) (T b) (l t).toNNReal ((V' b).leaf s y₀)); have he(t)(ht:0≤l t):inner ℂ (H.leaf s x) (ramble X.val b t (H.leaf s y))=f t:=light Y h s W' R A S' a H x y X V' T b p x₀ y₀ ℓ₀ μ t ht
 have hv:Continuous l := continuous_const.add continuous_subtype_val; have hl: 0<l 0:=lt_of_lt_of_le (show 0<spinT L s 1 from (slot_zero L s) ▸ slot_strict L s (by decide : (0:ℤ)<1)) (show spinT L s 1 ≤ spinT L s 1+(0:ℝ) from by simp only [add_zero, le_refl])
 have hx:=he 0 hl.le; rw [ramble_zero] at hx; change inner ℂ (H.leaf s x) (H.leaf s y)=f 0 at hx; rw [hx]; refine (show Continuous f from continuous_const.inner (((regular_all Y h W' R A S' b (V' b) (T b) _).comp continuous_real_toNNReal).comp hv)) |>.tendsto 0 |>.congr' ?_
 filter_upwards [(hv.tendsto 0).eventually (Ioi_mem_nhds hl)] with z h; exact (he z (show 0< l z from h).le).symm
end
#print axioms blast
omit p
include B V' T
local notation "B₀" i:max=> planeP (GroupR X.val i)
include p
set_option maxHeartbeats 620000 in
omit S' T V' in
private lemma toll (v:∀ s:ℕ,∀ x y:D, Largess Y h a B x y→ inner ℂ (H.leaf s x) ((planeP (GroupR X.val B)) (H.leaf s y))=inner ℂ (H.leaf s x) (H.leaf s y)) (w:b∉ B)(k:Largess Y h a B x y)(t:VistaQ Λ.R.L): inner ℂ (Θ x) ((B₀ B) (ramble X.val b t (Θ y)))= inner ℂ (Θ x) (ramble X.val b t (Θ y)):=by
 obtain ⟨n,e,i,rfl⟩:=((eventually_ge_atTop s).and (frequentT _ t)).exists; obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le e; let x':=escalant Y h W' R a s j x; let y':=escalant Y h W' R a s j y; let η:b=a→0 ≤ i :=fun h=>(p h).elim; -- Elim? simpler
 have hc:= v (s+j) x' (hoist Y h a b i η y') (paving Y h a i x' y' B w η (preferable Y h s W' R a j x y B k))
 have hV:Θ x=H.leaf (s+j) x':=Eq.symm (escalate Y h s W' R a j H x); let U:=ramble X.val b (ticQ L (s+j) i); have hU: U (Θ y)= H.leaf (s+j) (hoist Y h a b i η y'):= (congrArg (fun v:H.space=> U v) (Eq.symm (escalate Y h s W' R a j H y))).trans (blast Y h (s+j) W' R a i H y' X b p)
 let e(v w:H.space):= inner ℂ v ((B₀ B) w); let f(v w:H.space):= inner ℂ v w
 exact (congrArg₂ e hV hU).trans (hc.trans (congrArg₂ f hV.symm hU.symm))
omit X p S' T V' in
private lemma tolH {F:Hilbert}{w':Side}(U:Terrace F w' a)(x y:F)(g:Tendsto (fun t=>inner ℂ x (ramble U b t y)) (𝓝 0) (𝓝 (inner ℂ x y))) (z:inner ℂ x ((planeP (GroupR U B)) y)=inner ℂ x y) (h:∀ t, inner ℂ x ((planeP (GroupR U B)) (ramble U b t y))=inner ℂ x (ramble U b t y)) : inner ℂ x (planeP (GroupR U (b::B)) y)=inner ℂ x y := by rw [widget,mul_apply_eq_comp,← z]; apply Hike.vocable U y x; rw [z]; exact g.congr' (Eventually.of_forall fun t=>(h t).symm)
private lemma tolG (k:Largess Y h a (b::B) x y): Tendsto (fun t=> inner ℂ (Θ x) (ramble X.val b t (Θ y))) (𝓝 0) (𝓝 (inner ℂ (Θ x) (Θ y))):=by
 let he:= k b List.mem_cons_self p
 let x': Decko Y h b:=⟨fire Kₜ b 0 (fire Kₜ a 0 x.val),he.1⟩; let y':Decko Y h b:= ⟨_,heat_light Y h b y.val he.2⟩
 exact glow Y h s W' R A S' a H x y X V' T b p x' y' rfl rfl
private lemma tollB (k':Largess Y h a (b::B) x y)(hm:b∉ B)(v:∀ s:ℕ,∀ x y:D, Largess Y h a B x y→ inner ℂ (H.leaf s x) ((planeP (GroupR X.val B)) (H.leaf s y))=inner ℂ (H.leaf s x) (H.leaf s y)) : inner ℂ (Θ x) ((planeP (GroupR X.val (b::B))) (Θ y))=inner ℂ (Θ x) (Θ y):=by
 have he:Largess Y h a B x y:=fun j t=> k' j (List.mem_cons_of_mem _ t); have hm₁:= v s x y he
 exact tolH a B b X.val _ _ (tolG Y h s W' R A S' a H x y B X V' T b p k') hm₁ (toll Y h s W' R a H x y B X b p v hm he)

omit p
lemma payment (d:B.Nodup) (p:Largess Y h a B x y): inner ℂ (Θ x) ((planeP (GroupR X.val B)) (Θ y))=inner ℂ (Θ x) (Θ y):=by
 induction B generalizing s x y with
 | nil=> rw [seat_group]; rfl
 | cons i t ih=>
    obtain ⟨hm,hT⟩:= List.nodup_cons.mp d; have he:Largess Y h a t x y:= fun j e=> p j (List.mem_cons_of_mem _ e)
    by_cases η:i=a
    · subst i; rw [time_id]; exact ih s x y hT he
    exact tollB Y h s W' R A S' a H x y t X V' T i η p hm (fun s x y=> ih s x y hT)
-- shape Largess incl.B.
#print axioms payment
omit B V' T X S'
open Eight Quest Quest.Chaperone Tint
local notation "k₁" a:max=> targetP Λ l a
lemma wealthy (S:Finset Cover) (p:Ahead a 0 (targetP Λ l k) S): Ahead a (tic Kₜ) (reserve Λ l) S:=fun i t=> by specialize p i t; unfold targetP at p; have hg:tic Kₜ=8*Λ.block.val:= rfl; rw [hg]; omega
local notation "ξ₀" => Anteroom X.val
local notation "F₀"=> Model Y h Φ s
lemma camWave (p:Ahead a (tic Kₜ) (reserve Λ l) S) (w: W (tent Y h))(v : Locator Kₜ w S): w∈ Portico Y h a := ⟨S,Ahead.subh S a (Nat.cast_nonneg _) p,v⟩
include X in
lemma goldStamp : inner ℂ (omegaV Y h W' R a H) (cpo ξ₀ (dip ξ₀ (Θ x))) = Model Y h Φ s x.val.val:=by rw [castC,←planeP_inner,inlet (include_unity X.val Terrace.scheduleL (gold_fixed Y h W' R a H X)),goldPrice, Modell] -- Modul
variable (hQ:∀ i:Axis,Ahead i 0 (targetP Λ l k) (refract i 0 T₁)) (hp:∀ i:Axis,Ahead i 0 (targetP Λ l k) S)
variable {σ τ:Window.Family}{L':Finset (Face ℤ)}
-- generic Probe Masse
include hQ hp
include B in
lemma quest (z:Locator Kₜ (fire Kₜ a 0 x.val) T₁)(p: Locator Kₜ y.val S): Largess Y h a B x y:=fun i _ _ => let g:= wealthy Y h k i S (hp i); let u:=refract i 0 T₁; ⟨⟨u,Ahead.subh u i (Nat.cast_nonneg _) (wealthy Y h k i u (hQ i)), locate_cold _ _ _ _ z⟩,S,g,p⟩ -- args wealthy
include X S' T V'
lemma runeAge (z:Locator Kₜ (fire Kₜ a 0 x.val) T₁) (p:Locator Kₜ y.val S) : inner ℂ (dip ξ₀ (Θ x)) (dip ξ₀ (Θ y))=Φ s (helve Kₜ a x.val y.val) := by rw [sightL,castC]; exact (payment Y h s W' R A S' a H x y Terrace.scheduleL X V' T (by decide) (quest Y h S T₁ k a x y Terrace.scheduleL hQ hp z p)).trans (H.measure ..) -- may decide need univ? Test
end OutK
end Mist
end YM.CF.Buffered.Afterglow.Hierarchy
