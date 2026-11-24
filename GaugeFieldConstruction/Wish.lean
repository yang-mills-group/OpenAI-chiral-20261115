import GaugeFieldConstruction.Virtue
/-!
# Free product normalized action
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration.RawBank
open Gap Cauchy Conj Row Phys Function Submodule U1 Flux One Stage Wide Stage.Cell One.Lamp Floor
open Matter (Slot FlavorIndex)
open scoped BigOperators Topology
variable (m :ℂ) (V : Bool→ℂ)

/-- Theangular actions agree on inclusion, because they charge at that same place. -/
lemma SY_up (d : Floor) (Ω : Rotors) (p : UV d): SY m V five Ω (lift d p)=lift d (SY m V d Ω p) := by
  obtain ⟨χ,c⟩:= allowance
  apply sub_eq_zero.mp; apply shine five; intro b
  have h:= stroke m V d p c Ω b; have h2:= stroke m V five (lift d p) c Ω b
  have he v : shells five (lift d v)=shells d v:= LinearMap.congr_fun (shell_lift d) v
  simp only [sub_zero] at h h2; rw [he] at h2
  rw [map_sub,map_sub,map_sub Wick.pair,LinearMap.sub_apply,map_sub,he,← h2,← h,sub_self]
lemma payΘ (k : Axis) : packΘ m V (basis k)=(LinearMap.prodMap 0 (LinearMap.prodMap (m • LinearMap.id) (LinearMap.prodMap
    (LinearMap.pi fun i : FlavorIndex=> V i.1 • (LinearMap.proj i : Fragment (UF five) →ₗ[ℂ] UF five)) 0))) ∘ₗ deriv k := by
  unfold packΘ; rw [Finset.sum_eq_single k];
  · simp
  · intro b _ v; rw [basis_eq, if_neg v,Complex.ofReal_zero,zero_smul] -- tune
  simp
lemma invoice_mul (t : ℂ) (p : Bool→ℂ) (l : Raw.Sym) (k:Axis) : packΘ m V (basis k) ((stress t p).val l)=
    deriv k ((stress (m*t) (V*p)).val l) := by
  rw [payΘ]; apply shell_in five; set a:=stress t p; set b:=stress (m*t) (V*p)
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change ((m • _ : UG five)).val=P_g k _
    have h:(b.val l).2.1.val=m • (a.val l).2.1.val:= by change (m*t) • bead.val l=m • t • bead.val l; rw [smul_smul]
    -- packages rfl
    change m • P_g k (a.val l).2.1.val= P_g k (b.val l).2.1.val; rw [h,map_smul]
  apply Prod.ext
  · ext1 i
    let g (u:ℂ) (w:Bool→ℂ):= ((stress u w).val l).2.2.1 i
    have e: ((g (m*t) (V*p)): UF four).val=V i.1 • (g t p).val:= by
      by_cases h:i.2.1=i.2.2
      · have he (u:ℂ) (w:Bool→ℂ): (g u w).val=w i.1 • strand.val l:=by
          unfold g; change (((backward four Raw.symAct _).val l).2.2.1 i).val = _; simp only [backward,Flavor.bundle_,h,if_true]; rfl
        rw [he,he,smul_smul]; rfl
      have he (u:ℂ) (w:Bool→ℂ): (g u w).val=0:=by
        change (((backward four Raw.symAct _).val l).2.2.1 i).val = _; simp only [backward,Flavor.bundle_, if_neg h]; rfl
      rw [he,he,smul_zero]
    change V i.1 • P_f k (g t p).val=P_f k (g (m*t) (V*p)).val; rw [e,map_smul]
  ext1 i; have h:(b.val l).2.2.2 i=0:= Subtype.ext ((Submodule.mem_bot ℂ).mp ((b.val l).2.2.2 i).property)
  change 0=P_x k ((b.val l).2.2.2 i).val; rw [h,Submodule.coe_zero,map_zero]
end YM.GaugeFieldConstruction.Calibration.RawBank
