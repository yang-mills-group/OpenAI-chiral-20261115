import YM.SU5.FiniteGaugeData.Hills.Grove
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
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey
namespace Hills
variable (a b:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)(B:Repertory Y h W' R b)(p:a≠b)
local notation "F"=> Camera Y h a W' R A
local notation "G"=> Camera Y h b W' R B
local notation "X" s:max=> route Y h s a W' R A
local notation "V" s:max=> route Y h s b W' R B
local notation "U"=> Sync (Pears Y h a b W' R A B)
local notation "Ω"=> orbitSeed Y h a W' R A
-- canonical ID of joint ground spaces across axes THAT MAY NOT have any SO4 isomorphism. Uses all-tick hierarchy identity.
abbrev TeaHouse (K:Calibration):= ((ℕ × W K) →₀ ℂ)
local notation "D"=> TeaHouse Kₜ
local notation "Θ"=> orbitSeed Y h a W' R A
local notation "Ψ"=> orbitSeed Y h b W' R B
abbrev dozen : TeaHouse Kₜ→ₗ[ℂ]Camera Y h a W' R A:= Finsupp.linearCombination ℂ fun (p:ℕ× W Kₜ)=> ((X p.1) p.2 Θ)
local notation "B₀"=> dozen Y h a W' R A
local notation "B₁"=> dozen Y h b W' R B
include A
lemma host_day (s:ℕ)(f:W (tent Y h)): dozen Y h a W' R A (Finsupp.single (s,f) 1)=(X s) f Θ:=by unfold dozen; rw [Finsupp.linearCombination_single,one_smul]
lemma expanse : DenseRange (dozen Y h a W' R A):= Dense.mono (s₁:=Set.range (fun x:Playlist.Show.Vect Y h a 0=> dip (StructureH Y h a W' R A).Unity (A.paid x))) (by
 rintro x ⟨w,rfl⟩; obtain ⟨k,e⟩:= (eventual_table Y h W' R a A w).exists; dsimp only at e ⊢; rw [←e,← exhibit,← host_day Y h a W' R A k]; exact ⟨_,rfl⟩) (seed_whole Y h a W' R A)
include B p
lemma imbued (x:W Kₜ)(y:W Kₜ): inner ℂ ((X s) x Θ) ((X i) y Θ) = inner ℂ ((V s) x Ψ) ((V i) y Ψ) := by
 have he:= meet_x Y h 0 a b W' R A B (1:W Kₜ); rw [route_nil,route_nil] at he; exact award_e Y h s i a b W' R A B p x y he -- maybe needs simp because 1 apply defeq
lemma comparableL (x z:D): inner ℂ (B₀ x) (B₀ z)= inner ℂ (B₁ x) (B₁ z):=by
 induction x using Finsupp.induction_linear with
 | zero=> simp
 | add x y p q=> rw [map_add,map_add,inner_add_left,inner_add_left,p,q]
 | single x c=> induction z using Finsupp.induction_linear with
               | zero=> simp
               | add w v p q=> rw [map_add,map_add,inner_add_right,inner_add_right,p,q]
               | single y d=> obtain ⟨s,v⟩:=x; obtain ⟨i,u⟩:=y; unfold dozen; simp only [Finsupp.linearCombination_single,inner_smul_right,inner_smul_left,imbued Y h s i a b W' R A B p v u]
def flowsH : (Camera Y h a W' R A) ≃ₗᵢ[ℂ] (Camera Y h b W' R B):= (LinearEquiv.refl ℂ (TeaHouse Kₜ)).extendOfIsometry (B₀) (B₁) (expanse Y h a W' R A) (expanse Y h b W' R B) fun x=>by
 change ‖(B₁) x‖ = _; rw [norm_eq_sqrt_re_inner (𝕜:=ℂ),norm_eq_sqrt_re_inner (𝕜:=ℂ),comparableL Y h a b W' R A B p x]
lemma flows_at (x:TeaHouse (tent Y h)): flowsH Y h a b W' R A B p (B₀ x)= B₁ x:=by unfold flowsH; rw [LinearEquiv.extendOfIsometry_eq]; rfl
lemma flows_seed (x:W (tent Y h)): flowsH Y h a b W' R A B p ((X s) x Θ)=(V s) x Ψ:=by rw [←host_day, flows_at,host_day]
lemma lives_origin : flowsH Y h a b W' R A B p (orbitSeed Y h a W' R A)=orbitSeed Y h b W' R B:= by have he:= flows_seed Y h 0 a b W' R A B p (1:W Kₜ); rw [route_nil,route_nil] at he; exact he
lemma flows_m (f:W (tent Y h))(x:F) : flowsH Y h a b W' R A B p ((X s) f x)= (V s) f (flowsH Y h a b W' R A B p x):= by
 let T' := flowsH Y h a b W' R A B p; let x':= (X s) f; let y:= (V s) f
 have he (u:Playlist.Show.Vect Y h a 0) :
      let v₀ := dip (StructureH Y h a W' R A).Unity (A.paid u)
      T' (x' v₀)= y (T' v₀):= by
    intro r; obtain ⟨n,e⟩:= (eventual_table Y h W' R a A u).exists; dsimp only at e; unfold r; rw [←e, ←exhibit]; apply phase_ext Y h b W' R B; intro k t; unfold T'; rw [flows_seed,←flows_seed Y h k a b W' R A B p, LinearIsometryEquiv.inner_map_map]; -- RHS v_k also rewrit? `rw` only lhs and rhs? 
    rw [award_e Y h k n a b W' R A B p _ _ (meet_x Y h s a b W' R A B f)]
    rw [flows_seed]
 apply congr_fun (?_ : (fun x=>T' (x' x))=(fun x=> y (T' x))) x
 exact (seed_whole Y h a W' R A).equalizer (T'.continuous.comp x'.continuous) (y.continuous.comp T'.continuous) (funext he)

-- convenient use given Repertory profile independent all axes. global.choose common A(Ω.Agora). always ∃ X.I.Cover.Reset.Lifting.Post.K.
#print axioms flows_m
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
