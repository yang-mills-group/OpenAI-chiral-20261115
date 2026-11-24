import YM.SU5.Relativistic.StemRead
import YM.SU5.Relativistic.CarryBoundary
import YM.SU5.Relativistic.DiagonalBoundary
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P₀" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history

variable {s n:ℕ}
local notation "μ" z:max=> gaugeShift Λ.block z
local notation "E₀" s:max f:max=> Lariat.rideL Y H T s f


open Lariat
section weights
variable (M:Panel Y H D.univ_ G.history G.clipped d false (c d)) (y:M.X)
variable (A:∀ i:ℕ, Future Y H d i)(p: Subscriber Y H D G d c M y A)
local notation "o" d:max f:max i:max=> Lariat.parcel Y H d (A i) s f -- s implicit heights? local
local notation "Ξ₀" s:max=>appeal Y H D G d c (M.character y) T s
local notation "τ₁" f:max z:max n:max=> s+(n+((A z).t-(s+n+1))+1)
include t p
lemma electable (s:ℕ)(f:Lariat (tent Y H) n):
    Tendsto (fun i:ℕ=> Lariat.discount E (hue (Lariat.parcel Y H d (A i) s f)) (s+(n+((A i).t-(s+n+1))+1)) (rideL Y H T s (Lariat.parcel Y H d (A i) s f))) atTop (𝓝 ((Ξ₀ s) f)):=by
 unfold Lariat.appeal
 simp_rw [parcel_turn]
 by_cases h:hue f=false
 · simp_rw [h,Lariat.discount,if_neg Bool.false_ne_true]
   let P:=rideL Y H T s f; let F:D₀:=⟨P,aux_test (show InTest K true (Lariat.box Λ l f) false P from h ▸ aboard Y H u T t s f)⟩; let z:Ξ:= pinhole D₀ (s+n) F; have ht:= p.focus z (Altitude.curve.mpr ⟨s+n,Altitude.short_pinhole (s+n) F⟩)
   unfold z at ht; rw [plugged] at ht; apply ht.congr'; filter_upwards [eventually_gt_atTop (s+n)] with i x; obtain ⟨hq,hz⟩:= pad_consult Y H D G u t d (A i) s f h (lt_of_lt_of_le x (A i).arrival); exact hz.symm
 have hx:f.hue=true:=Bool.eq_true_of_not_eq_false h; simp_rw [hx]; exact tendsto_const_nhds

-- bases countably budgeted (NOT countably many marks)
abbrev Minuts:= Σ _:Fin (1), (Σ n:ℕ,ℕ×ℕ×(Fin (n+1)→ Finset Cover)) -- `1` just remove
noncomputable def seize : ℕ → Minuts:= (exists_surjective_nat Minuts).choose
private def denude {n:ℕ}(X: Fin (n+1) → Finset Cover)(i:ℕ): Finset Cover:= if p:i<n+1 then X ⟨i,p⟩ else ∅

-- measures for all consultants. single index pair u etc.
local notation "I₁"=> a ∘ G.rows ∘ u
local notation "K₁"=> b ∘ G.columns ∘ u
omit p -- actually not used
include D
lemma commercial (i s n:ℕ) (F:ℕ→Finset Cover) (C:ℕ)(e:ℝ)(h:0<e): ∀ᶠ r:ℕ in atTop, let y:= (A i).t; let v' := n+(y-(s+n+1))+1; let f' : Lariat (tent Y H) n → Lariat (tent Y H) v' := Lariat.parcel Y H d (A i) s
              ∃ S,Tapestry.Pay Y (s+v') (I₁ r) (K₁ r) ∧ Lariat.dues_i Y H s (I₁ r) S v' ∧ ∀ f: Lariat (tent Y H) n,Costs F f→ priced (fun _=> (C:ℝ)) f→ Costs S (f' f) ∧ ‖sharp Y H (s+v') (I₁ r) (K₁ r) (priceAt Y H s (I₁ r) (K₁ r) (f' f))-Lariat.discount E (hue (f' f)) (s+v') (rideL Y H T s (f' f))‖≤e :=by
 let v':= n+((A i).t-(s+n+1))+1
 obtain ⟨p₀,Z,g,k⟩:=parcel_fac Y H d (A i) n s F C
 have hT:= t.thins.tendsto_atTop
 have ht:= (t.thins.tendsto_atTop.eventually (G.history.finance (s+v')))
 have hS:Tendsto I₁ atTop atTop:= D.univ_.pick.grow_i.tendsto_atTop.comp (G.history.growsA.tendsto_atTop.comp hT)
 filter_upwards [hS.eventually (packsEnough Y H s Z v'),ht,Lariat.admits_all Y H V G.history u T t s v' Z p₀ g e h] with i' hw uxx v
 refine ⟨Z,⟨uxx.depth,uxx.enters⟩,hw,fun f i j=>⟨(k f i j).1,v _ (k f i j).1 (k f i j).2⟩⟩

-- preserve CP2 Eχ at pin level when weighted argument extended. Distant prepares state.
include t p
structure Subscribed (u:ℕ→ℕ)(T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)) (A:∀ i,Future Y H d i)(w:ℕ→ℕ): Prop where
 worker : StrictMono w
 move (n s:ℕ)(f:Lariat (tent Y H) n):
    Tendsto (fun i=> let g:=Lariat.parcel Y H d (A i) s f; let r:= a (G.rows (u (w i))); let v:=b (G.columns (u (w i))); sharp Y H (s+(n+((A i).t-(s+n+1))+1)) r v (priceAt Y H s r v g)) atTop (𝓝 (appeal Y H D G d c (M.character y) T s f))
 calibrated (n s:ℕ)(f:Lariat (tent Y H) n): ∀ᶠ i in atTop, let Y':=(A i).t; let g:=Lariat.parcel Y H d (A i) s f; let r:= a (G.rows (u (w i))); let v:=b (G.columns (u (w i))); s+n < Y' ∧ ∃ S,Tapestry.Pay Y (s+(n+(Y'-(s+n+1))+1)) r v ∧ Lariat.dues_i Y H s r S (n+(Y'-(s+n+1))+1) ∧ Costs S g -- proof pay & ∃ grid line

lemma enquiring : ∃ w:ℕ→ℕ, Subscribed Y H D G d c M y u T A w:=by
 let P (i:ℕ) (K':Minuts)(r:ℕ):Prop:= let z:=K'.2; let n:=z.1; let s:=z.2.1; let A':=(A i).t; let m:=n+(A'-(s+n+1))+1; let p:=fun f:Lariat (tent Y H) n=> Lariat.parcel Y H d (A i) s f
                                      ∃ S,Tapestry.Pay Y (s+m) (I₁ r) (K₁ r) ∧ Lariat.dues_i Y H s (I₁ r) S m ∧ ∀ f,Costs (denude z.2.2.2) f→ priced (fun _=> (z.2.2.1:ℝ)) f→ Costs S (p f) ∧ ‖sharp Y H (s+m) (I₁ r) (K₁ r) (priceAt Y H s (I₁ r) (K₁ r) (p f))-Lariat.discount E (hue (p f)) (s+m) (rideL Y H T s (p f))‖≤propeller i
 obtain ⟨w,z,x⟩:=agenda (fun i r=>∀ n ∈Finset.Iic i,P i (seize n) r) (fun i=> (eventually_all_finset _).mpr fun j _=> commercial Y H D G u t d A i _ _ _ _ (propeller i) (by unfold propeller; positivity)) -- commercial implicit M y? omitted. 
 have hp(k:Minuts):∀ᶠ i in atTop,P i k (w i):=by obtain ⟨i,h⟩:= (exists_surjective_nat Minuts).choose_spec k; have he:seize i=k:=h; filter_upwards [eventually_ge_atTop i] with j t; rw [←he]; exact x j i (Finset.mem_Iic.mpr t)
 have hm {n:ℕ}(f:Lariat K n):∃ (K0:Fin (n+1)→Finset Cover)(r:ℕ), Costs (denude K0) f ∧ priced (fun _=> (r:ℝ)) f := by
    obtain ⟨X,p⟩:= Lariat.boards _ f; obtain ⟨r,h⟩:=Lariat.sizes Y H f
    exact ⟨fun i=> X i,r,Lariat.hiresYear p (fun i t=>(show X i=denude (fun (i:Fin (n+1))=> X i) i from by unfold denude; rw [dif_pos (show i < n+1 from by omega)])),h⟩
 refine ⟨w,z,fun n s f=>?_,fun n s f=>?_⟩
 · obtain ⟨F,n',e,H'⟩:=hm f; let L':Minuts:=⟨0,n,s,n',F⟩
   refine transfer_price _ propeller_fades (electable Y H D G u t d c M y A p s f) ?_
   filter_upwards [hp L'] with i r; obtain ⟨S,w,e',h⟩:=r; exact (h _ e H').2
 obtain ⟨F,n',e,H'⟩:=hm f; filter_upwards [hp ⟨0,n,s,n',F⟩,eventually_gt_atTop (s+n)] with i r g
 obtain ⟨S,w,p,h⟩:=r; exact ⟨lt_of_lt_of_le g (A i).arrival,S,w,p,(h _ e H').1⟩
end weights

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
