import YM.SU5.May.FloeLaps
import YM.SU5.May.FloeStock
import YM.SU5.May.FloeCore
import YM.SU5.May.FloeCourse
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
local notation "T" n:max => Therapies.paceFloor Y H G n
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
open Flare Personality PriceCliff
open Reed (Fine think)
-- arbitrary finite S, polar phases from ANY reps (period e.g. parity signs true), not requiring Hosp.
private lemma samplers (N:Side)(i:Single N)(u:i∈ modesIn N (Satin.region U N)): ∃ x:Cover,nodeC x∈ U∧ wrap N x=i.1.1:=by
 obtain ⟨y,ys,e⟩:= Finset.mem_image.mp ((modes_at ..).1 u); let x:=i.1.1; change wrap (More N) y=node x at e
 -- proof as in Dic but no need for Hosp.
 let b:=nodeC (natural x)
 have hb: wrap (More N) y=wrap (More N) b:=by rw [e]; unfold b; rw [←node_of, Rush.nat_true]
 let d:= periods (More N) y-periods (More N) b
 have he:y = b + (More N).val • d:=by
    unfold d; have h1:=Rush.carrying (More N) y; have h2:=Rush.carrying (More N) b
    rw [hb] at h1; rw [smul_sub]
    grind
 let w:= natural x + N.val • d
 have hw:nodeC w=y := by
    unfold nodeC w; unfold b nodeC at he; rw [he]; rw [smul_add, smul_smul]; change _= (2:ℕ)•_+_+(N.val*2) • _; rw [Nat.mul_comm 2]; abel
 exact ⟨w,hw.symm ▸ ys, needle (by rw [node_of,hw]; exact e)⟩
noncomputable def stockings (z:SU.Slot)(i:SpinIdx):Personality:= if h:i∈ plusHalf then pureV false z i h else pureV true z i (Finset.mem_compl.mpr h)
noncomputable def portfolio := (Finset.univ: Finset (SU.Slot × SpinIdx)).image (uncurry stockings)
private lemma coinage {N:Side}{t:Cover}(i:SpinIdx)(z:SU.Slot):∃ c:ℂ,‖c‖=1 ∧ (think (Tset N)).term (Lifted.index N t i z)= c • ton (player N t 1 (stockings z i)):=by
 let w:= Lifted.winding N t; have h: ‖w‖=1:= fee_norm _; have e:w≠0:=norm_pos_iff.mp (h.symm ▸ (show (0:ℝ)<1 from zero_lt_one))
 have he:Hygrometry.pitch N t 1 z (basisKet i)=basisC N t i z:=by rw [Hygrometry.pitch,canto]; simp [Emu.gain]
 unfold stockings; split
 next v =>
    refine ⟨w⁻¹,by rw [norm_inv,h,inv_one],?_⟩; change _=w⁻¹ • create (Hygrometry.pitch N t 1 z (basisKet i)); rw [show (think (Tset N)).term (Lifted.index N t i z)=put (Lifted.index N t i z) from if_pos ((mem_Tset ..).mpr v)]; rw [he,basisC,map_smul,create_put]; exact (inv_smul_smul₀ e _).symm
 next v=>
    refine ⟨(star w)⁻¹,by rw [norm_inv,norm_star,h,inv_one],?_⟩; change _=(star w)⁻¹ • Fock.remove (- Hygrometry.pitch N t 1 z (basisKet i)); rw [show (think (Tset N)).term (Lifted.index N t i z)= -takeF (Lifted.index N t i z) from if_neg fun t=> v ((mem_Tset ..).mp t)]; rw [he,basisC]; unfold Fock.remove takeF; rw [map_neg, map_smul,star_neg,star_smul,smul_neg,create_put]; exact congrArg Neg.neg (inv_smul_smul₀ (by simpa using e: star w ≠ 0) _).symm
variable {P:Ramp}{N:Side}
abbrev SteamRoll (b:Bool)(κ:ℕ)(A:FC (Single N)){J:Type*} (π:J→ Cover)(X:J→Personality): Prop:= ∃ (α:Type) (_:Fintype α)(S:α→List J)(V:α→ℂ), (∀ i,(S i).length ≤ κ ∧ wheat (S i)=b) ∧ A=utter π X N 1 S V -- premise uses local j.
variable {b:Bool}
private lemma roll_any (u:FC (Single N))(v:u∈ SpinLen (Tset N) (modesIn N (Satin.region U N)) b κ) {J:Type*}{π:J→ Cover}{X:J→Personality}(p:∀ i:Single N,i∈ modesIn N (Satin.region U N) → ∃ (j:J)(c:ℂ), (think (Tset N)).term i= c • ton (player N (π j) 1 (X j))): SteamRoll b κ u π X:= by
 refine Submodule.span_induction (p:=fun f _=> SteamRoll b κ f π X) ?_ ?_ ?_ ?_ (show u∈ Submodule.span _ _ from v)
 · intro f i; obtain ⟨C,q,rfl⟩:= i
   have h(C:List (Single N))(q:∀ i∈ C,i∈ modesIn N (Satin.region U N)): ∃ (C':List J) (c:ℂ), C'.length=C.length ∧ rollC (think (Tset N)).term C=c • literal π X N 1 C':=by
      induction C with
      | nil=> exact ⟨[],1,rfl,(one_smul ℂ (1: FC (Single N))).symm⟩
      | cons i m ih=>
        obtain ⟨j,c,a⟩:=p i (q i List.mem_cons_self); obtain ⟨C,d,h,g⟩:=ih (fun j t=>q j (List.mem_cons_of_mem i t)); refine ⟨j::C,c*d,by simp [h],?_⟩; change (think (Tset N)).term i * rollC (think _).term m=(c*d) • (ton _ * literal _ _ N 1 C); rw [a,g,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
   obtain ⟨d,e,h,g⟩:=h C q.touches; exact ⟨Unit,inferInstance,fun _=>d,fun _=>e,fun i=> ⟨h.symm ▸ q.limbs,by rw [←q.color,wheat_grade,wheat_grade,h]⟩,(by simpa [utter] using g)⟩
 · exact ⟨Fin 0,inferInstance,fun _=>[],fun _=>0,fun i=>i.elim0,by simp [utter]⟩
 · rintro f g - - ⟨K,t,F,w,e,rfl⟩ ⟨L,l,Y,k,d,rfl⟩ -- tune Exists binder count
   refine ⟨K⊕L,inferInstance,Sum.elim F Y,Sum.elim w k,fun i=> by cases i<;> (first | apply e | apply d),?_⟩
   simp only [utter,Fintype.sum_sum_type, Sum.elim_inl,Sum.elim_inr]
 · rintro s g - ⟨K,t,F,v,e,rfl⟩
   refine ⟨K,t,F,s • v,e,?_⟩; simp only [utter,Finset.smul_sum, smul_smul, Pi.smul_apply,smul_eq_mul]
noncomputable def Demands (κ:ℕ) (U: Finset Personality)(b:Bool)(f: Mark N)(P:Ramp)(Λ: Preparation)(Z:ℝ): Prop:= ∃ (J:Type)(_ : LinearOrder J)(_ : Fintype J) (α:Type) (_:Fintype α) (π:J→ Cover)(X:J→Personality)(F:α→ List J)(w:α→ℂ),PagePermit (Λ:=Λ) U P κ N b f π X F w ∧ Z=∑ i,‖w i‖
-- labels never need full Tor (would demand clearance for non‐support)
lemma rank_purchase (f:Mark N)(v:f (1,1)∈ SpinLen (Tset N) (modesIn N (Satin.region U N)) b κ)(h:∀ x:Cover,nodeC x∈U→Clear P Λ.K.j x)(s:∀ x y:Cover,nodeC x∈U→nodeC y∈U→ Smallish N ((whisper P).cell x-y)):∃ a:ℝ,Demands κ portfolio b f P Λ a := by
 let J:= ↥(modesIn N (Satin.region U N)); let Z(i:J): Single N:= i.val; have hx(i:J):∃ x:Cover,nodeC x∈U∧ Lifted.index N x (Z i).1.2 (Z i).2=Z i:=by obtain ⟨x,e,v⟩:= samplers N i.val i.property; refine ⟨x,e,Prod.ext ?_ rfl⟩; exact Prod.ext v rfl
 choose π H H' using hx; let Y(i:J):= stockings (Z i).2 (Z i).1.2
 have hp(i:J): ∃ c:ℂ,(think (Tset N)).term (Z i)=c • ton (player N (π i) 1 (Y i)):=by obtain ⟨c,-,t⟩:=coinage (t:=π i) (N:=N) (Z i).1.2 (Z i).2; rw [H'] at t; exact ⟨c,t⟩
 obtain ⟨β,u,T',F,e,d⟩:=roll_any κ _ v (X:=Y) (π:=π) (by intro i k; exact ⟨⟨i,k⟩,hp ⟨i,k⟩⟩)

 refine ⟨_,J,inferInstance,inferInstance,β,u,π,Y,T',F,⟨fun i=>?_, fun i=>h (π i) (H i), fun i j=>s (π i) (π j) (H i) (H j),fun i=>(e i).1,fun i=>(e i).2,d⟩,rfl⟩
 exact Finset.mem_image.mpr ⟨((Z i).2,(Z i).1.2),Finset.mem_univ _,rfl⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.rank_purchase
