import YM.Next.FOUNDATIONS.Primary
namespace YM.Next.FoundationVerification
def Target : Prop := ∀ G : YM.Gauge, YM.Bid.Learns G (YM.Next.Foundations.hol G) (YM.Labels.frames G)
theorem checked : Target := YM.Next.Foundations.learns
end YM.Next.FoundationVerification
