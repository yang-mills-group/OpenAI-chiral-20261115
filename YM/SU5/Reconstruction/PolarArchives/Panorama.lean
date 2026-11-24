import YM.SU5.Reconstruction.PolarArchives.Together
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
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
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "au"=>move K
variable (P:Ramp)
local notation "H₀"=> Ark.Ht Y H G.history.circuit P.a 0 false (C P.a)
local notation "A"=>Aurora Y H V G.history P.a false (C P.a)
local notation "Pc"=>album Y H V G C P.a
local notation "pay"=> LightBudget.prepaid Y H V G P.a (C P.a)
local notation "vc"=>seat0 Y H V G.history P.a false (C P.a)
local notation "px"=> (A).orthogonalProjectionOnto
local notation "Nₐ"=> Domain Y H G false (flank P.a 0)
local notation "τ" => gust P (tent Y H)
open Chambers
local notation "μₜ" t:max=>move (tent Y H) (eject P.a t)
variable {q:Bool}{U:Set RSpace}
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Hₛ"=> groundRoom Y H V G.history P.a false (C P.a)
local notation "Ωχ"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Rs"=> reduceToDisplay Y H V G.history G.clipped P.a false (C P.a)
local notation "RX"=>rotateQ P K
local notation "VR"=> Veer Y H V G P
local notation "TT"=> Tango Y H V G P
local notation "C₀" p:max=> (Pc p).val
local notation "FZ" p:max=> (Pc p).val vc
noncomputable def unity : Domain Y H G false Set.univ:= ⟨1,domain_one ..⟩
lemma unit_archive : Pc (unity Y H G) = 1:=by
 let v:= ticket_one Y H G 0
 rw [show (unity Y H G)=⟨ticket Y H G 0 1,ticket_loose ..⟩ from Subtype.ext v.symm,atStamp,map_one,located_one]
lemma turning_units : TT (unity Y H G)=unity Y H G := Subtype.ext (gust_unit ..)
lemma lcd(x:Beacon (tent Y H) false): ∃ y:Domain Y H G false Set.univ,instrument Y H V G.history G.clipped P.a false (C P.a) x = (Pc y).val:=by
 let f: Dome (tent Y H):=⟨x.2.val,x.2.property.1⟩
 refine ⟨⟨ticket Y H G x.1 f,ticket_loose ..⟩,?_⟩
 rw [atStamp]; rfl
lemma archives : DenseRange (fun v:Domain Y H G false univ=> (Pc v).val vc):= by
 refine (compressed_dense Y H V G.history G.clipped P.a false (C P.a)).mono ?_; rintro _ ⟨a,rfl⟩; obtain ⟨d,e⟩:= lcd Y H V G C P a; dsimp only; rw [e]; exact ⟨_,rfl⟩
lemma rayarchives : DenseRange (fun v:Domain Y H G false univ=> (Pc (VR v)).val vc):= by
 apply (archives Y H V G C P).mono; rintro _ ⟨k,rfl⟩; refine ⟨VR k,?_⟩; dsimp only; rw [(newsTags Y H V G C P k).2]
private lemma grams_at_root (p q:Domain Y H G false univ): inner ℂ (FZ p) (FZ q)=inner ℂ (FZ (VR p)) (FZ (VR q)) :=by
 have b:= partner Y H V G C P (VR p) q (unity Y H G)
 rw [turning_units,(newsTags Y H V G C P p).2, unit_archive] at b
 change inner ℂ _ (FZ q)= starRingEnd ℂ (inner ℂ (FZ (VR q)) (FZ (VR p))) at b -- FZ? order cost investigate
 exact b.trans (inner_conj_symm (𝕜:=ℂ) ..)
-- exact panel authority.No presumption φ itself respects it.
noncomputable def helm: groundRoom Y H V G.history P.a false (C P.a) ≃ₗᵢ[ℂ] groundRoom Y H V G.history P.a false (C P.a) :=
 (gram_impl («A»:=groundRoom Y H V G.history P.a false (C P.a)) (B:=groundRoom Y H V G.history P.a false (C P.a)) (archives Y H V G C P) (rayarchives Y H V G C P) (grams_at_root Y H V G C P)).choose
local notation "Lt"=> helm Y H V G C P
lemma dispatched (p:Domain Y H G false Set.univ): Lt (FZ p)= (Pc (VR p)).val vc:= (gram_impl («A»:=groundRoom Y H V G.history P.a false (C P.a)) (B:=groundRoom Y H V G.history P.a false (C P.a)) (archives Y H V G C P) (rayarchives Y H V G C P) (grams_at_root Y H V G C P)).choose_spec p
lemma returner (p:Hₛ): Lt (Lt p)=p:=by
 refine congrFun ((archives Y H V G C P).equalizer ((Lt).continuous.comp (Lt).continuous) continuous_id ?_) p
 funext x; change Lt (Lt (FZ x))=_; rw [dispatched,dispatched,(newsTags Y H V G C P x).2]; rfl -- tune id
lemma helm_vac : Lt vc= vc:=by
 have e:=dispatched Y H V G C P (unity Y H G)
 rw [show VR (unity Y H G) = unity Y H G from Subtype.ext (show RX (1 : Sky (tent Y H)) =1 from ?_),unit_archive] at e; exact e
 change flipMark P.a K (τ 1)=1; rw [gust_unit,flipMark_unit]

local notation "Gx"=> (Lt).conjStarAlgEquiv
private lemma pearl (M:Hilbert)(U:M≃ₗᵢ[ℂ] M)(T:M.Op)(u v w x:M)(p:U u=v)(q:U w=x): inner ℂ v (U (T (U.symm x)))=inner ℂ u (T w):= by subst_vars; rw [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]
private lemma adjCost (M:Hilbert)(T:M.Op)(x y:M): star (inner ℂ x ((star T) y))=inner ℂ y (T x):=by
 change starRingEnd ℂ (inner ℂ x ((star T) y)) = _; rw [inner_conj_symm]; exact ContinuousLinearMap.adjoint_inner_left ..
lemma makeshift(w:Domain Y H G false univ): Gx (C₀ w)= (Pc (VR w)).val := by
 apply DFunLike.coe_injective; apply (rayarchives Y H V G C P).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
 funext x; apply (rayarchives Y H V G C P).eq_of_inner_right ℂ; intro y; change inner ℂ (FZ (VR y)) (Lt ((C₀ w) ((Lt).symm (FZ (VR x))))) = inner ℂ (FZ (VR y)) ((C₀ (VR w)) (FZ (VR x)))
 have h:= partner Y H V G C P (VR y) x w
 rw [(newsTags Y H V G C P y).2] at h
 calc
 _ = inner ℂ (FZ y) ((C₀ w) (FZ x)) := pearl (Hₛ) Lt (C₀ w) _ _ _ _ (dispatched Y H V G C P y) (dispatched Y H V G C P x)
 _ = _ := h.trans (by rw [(newsTags Y H V G C P w).1]; exact adjCost (Hₛ) (Pc (VR w)).val (FZ (VR x)) (FZ (VR y))) -- check adjoint eq direction
lemma consign (x: displayAlgebra Y H V G.history G.clipped P.a false (C P.a)): Gx x.val∈ K₀:=by
 let e:= (Gx).toStarAlgHom; have Hk: IsClosed ((K₀).comap e : Set (Hₛ).Op):= (displayClosed Y H V G.history G.clipped P.a false (C P.a)).preimage (show Continuous e from open CStarAlgebra in map_continuous e)
 change x.val∈ (K₀).comap e; apply (StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le (s:=Set.range (instrument Y H V G.history G.clipped P.a false (C P.a))) ?_) Hk) x.property
 rintro _ ⟨k,rfl⟩; obtain ⟨w,h⟩:= lcd Y H V G C P k; rw [h]; change Gx (C₀ w) ∈ K₀; rw [makeshift]; exact (Pc _).property
lemma haul(w: (Hₛ).Op): Gx (Gx w)=w:=by
 ext1 x; have h(x:Hₛ): (Lt).symm x=Lt x:= (Lt).injective (by rw [LinearIsometryEquiv.apply_symm_apply,returner]); change Lt (Lt (w ((Lt).symm ((Lt).symm x))))=_; rw [h,h,returner,returner]
noncomputable def orbit: displayAlgebra Y H V G.history G.clipped P.a false (C P.a) ≃⋆ₐ[ℂ] displayAlgebra Y H V G.history G.clipped P.a false (C P.a):= by
 let f := ((Gx).toStarAlgHom.comp (K₀).subtype).codRestrict _ (consign Y H V G C P)
 have h : ∀ x:K₀,f (f x) = x :=fun x=> Subtype.ext (haul Y H V G C P x.val)
 exact StarAlgEquiv.ofBijective f ⟨Involutive.injective h,Involutive.surjective h⟩
local notation "α"=> orbit Y H V G C P
lemma orbit_lift(w:Domain Y H G false Set.univ): orbit Y H V G C P (album Y H V G C P.a w)=album Y H V G C P.a (VR w):=Subtype.ext (makeshift Y H V G C P w)
lemma orbit_square (x:K₀): α (α x)=x:= Subtype.ext (haul Y H V G C P x.val)
lemma orbit_cost (x:K₀): inner ℂ vc ((α x).val vc)= inner ℂ vc (x.val vc):=by
 change inner ℂ vc (Lt (x.val ((Lt).symm vc)))= _; rw [← helm_vac Y H V G C P, LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]; rw [helm_vac]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
