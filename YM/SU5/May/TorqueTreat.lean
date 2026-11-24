import YM.SU5.May.TorqueShift
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.TorqueBeam
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "Ω" => Complex.I
open May.Floe
open Buffered Buffered.Advance Buffered.Advance.Whorl May.Arctic
variable {K: Pressure.Teller group} {P: Patch}{B:Side}{e:ℝ}{Y: Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(h:1≤K.j) (p:Pearl A) (u:Stamped K.j P.L P.odd_side Y)
variable {m:Side}(R:Ramp)(M:Jill.Male)(k:A.roundZ ≤ (CSide m B).val)(w:Pad K.j (CSide m B))
variable {α:Type*} (X:α→ Reader0 (Single (CSide m B)))
local notation "N"=> CSide m B
local notation "Σ"=> changeM (m:=m) A 1 M
local notation "U"=> R.vehicle (CSide m B)
local notation "S"=> Tset (CSide m B)
local notation "K₀"=> ledger (CSide m B) K.j M
variable {W:Finset (Single (CSide m B))} (ρ δ:ℝ) (hw:∀ i,Worth (Tset (CSide m B)) W ρ (X i))(pc:0≤ρ) (dC:0≤δ)
variable {β:Type*}[Fintype β](F:β→List α)(w':β→ℂ)(b:Bool)(t:∀ i,wheat (F i)=b)
variable (B₁:ℝ) (hc:‖ledger (CSide m B) K.j M‖≤ B₁)(v:∀ (b:Bool)(x:Ket (Single (CSide m B))), withinM (if b then (Tset (CSide m B))ᶜ else Tset (CSide m B)) x → withinM W x → -(δ*‖x‖^2) ≤ (promoted (R.vehicle (CSide m B)) (ledger (CSide m B) K.j M) 0 (b,x) (b,x)).re)
include g h p u w k hc pc dC v
lemma warded {C:ℝ}{κ:ℕ}{b:Bool}{f: FC (Single (CSide m B))} (a:f∈ Capital (Tset N) W b κ ρ C): -(rimeCost κ (1+(B₁+δ)*ρ^2)*(δ*ρ^2)*C^2) ≤ (SpinPrice Σ (poseX (whisper R) b f)).re:=by
 obtain ⟨J,hℓ,F,w',p',q,rfl⟩:=a
 let ℐ:= Reader0 (Single N); let D: Finset ℐ:= Finset.univ.biUnion fun j: J=> (F j).toFinset
 let α₀:= ↥D; let Y(i:α₀):= (i.val:Reader0 (Single N)); let _:LinearOrder α₀:= LinearOrder.lift' (Fintype.equivFin α₀) (Fintype.equivFin α₀).injective -- types regular
 let P:∀ i:α₀,Worth (Tset N) W ρ (Y i):=fun i=> by obtain ⟨t,f,a⟩:=mem_biUnion.mp i.property; exact (p' _).allKeys i.val (List.mem_toFinset.mp a)
 have hx(i:J):∃ X:List α₀,X.map Y= F i:=by
    let Vtop(v:{j// j∈ F i}) : α₀:= ⟨v.1,mem_biUnion.mpr ⟨i,mem_univ _,List.mem_toFinset.mpr v.property⟩⟩
    refine ⟨(F i).attach.map Vtop,?_⟩; rw [List.map_map,show Y∘Vtop=Subtype.val from rfl,List.attach_map_subtype_val]
 choose G H using hx; have hL(j:J): (G j).length=(F j).length:=(by rw [←H,List.length_map]); have hx' : ∑ i: J,w' i • rollC ton (F i)=∑ i: J, w' i • rollC (ton∘Y) (G i):=sum_congr rfl fun i _=>congrArg (w' i • ·) (by rw [← H]; simp [rollC]); rw [hx'];
 let n:= 1+(B₁+δ)*ρ^2
 have hn:0≤B₁:=(norm_nonneg _).trans hc
 refine le_trans (neg_le_neg (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _=> norm_nonneg _) q _) (by unfold rimeCost; positivity))) (purchased A g h p u R M k w Y ρ δ P pc dC G w' b ?_ B₁ hc (coversHere A g h p u R M k w δ v) κ ?_)
 exact fun j=> by rw [←(p' j).poll,wheat_grade,wheat_grade,hL]
 intro j; rw [hL]; exact (p' _).size
lemma warded_now {C:ℝ}{κ:ℕ}{b:Bool}{f: FC (Single (CSide m B))} (a:f∈ Fort (Tset N) W b κ ρ C): -(rimeCost κ (1+(B₁+δ)*ρ^2)*(δ*ρ^2)*C^2) ≤ (SpinPrice Σ (poseX (whisper R) b f)).re:=by
 apply passFort (Z:=fun x=> (SpinPrice Σ (poseX (whisper R) b x)).re) isClosed_Ici _ _ a
 · let Z:= Σ; let Q:FC (Single N)→ₗ[ℂ] ℂ:=⟨⟨SpinPrice Z,fun v w=> SpinPrice.pair ..⟩,fun d u=>SpinPrice.cash ..⟩
   exact Complex.continuous_re.comp ((Q.continuous_of_finiteDimensional).comp ((continuous_const (y:=chord b)).smul ((theta_cont U).mul continuous_id))) -- `theta_cont` and U
 · exact fun _ h₁=> warded A g h p u R M k w ρ δ pc dC B₁ hc v h₁
#print axioms warded
#print axioms warded_now
end YM.CF.May.TorqueBeam
