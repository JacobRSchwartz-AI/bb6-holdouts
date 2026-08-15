terraform {
  required_version = ">= 1.5"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

variable "region" {
  default = "us-east-1"
}

# coqc is single-threaded and the build is -j1: single-core speed is all
# that matters (m7a/r7a = AMD Genoa, fastest EC2 single-thread).
# OdometerOrbit.v was OOM-killed at 31.5GB on a 32GB box; 128GB (plus
# the swapfile verify-remote.sh adds) is the measured-safe tier.
variable "instance_type" {
  default = "r7a.4xlarge"
}

provider "aws" {
  region = var.region
}

data "aws_ssm_parameter" "ubuntu2404" {
  name = "/aws/service/canonical/ubuntu/server/24.04/stable/current/amd64/hvm/ebs-gp3/ami-id"
}

# No SSH, no ingress: the box is driven entirely through SSM Run Command,
# and sources/results move through the transfer bucket.
resource "aws_s3_bucket" "xfer" {
  bucket_prefix = "bb6-verify-"
  force_destroy = true
}

resource "aws_iam_role" "verify" {
  name_prefix = "bb6-verify-"
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Allow"
      Action    = "sts:AssumeRole"
      Principal = { Service = "ec2.amazonaws.com" }
    }]
  })
}

resource "aws_iam_role_policy_attachment" "ssm" {
  role       = aws_iam_role.verify.name
  policy_arn = "arn:aws:iam::aws:policy/AmazonSSMManagedInstanceCore"
}

resource "aws_iam_role_policy" "xfer" {
  name_prefix = "xfer-"
  role        = aws_iam_role.verify.id
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect   = "Allow"
      Action   = ["s3:GetObject", "s3:PutObject"]
      Resource = "${aws_s3_bucket.xfer.arn}/*"
    }]
  })
}

resource "aws_iam_instance_profile" "verify" {
  name_prefix = "bb6-verify-"
  role        = aws_iam_role.verify.name
}

resource "aws_security_group" "verify" {
  name_prefix = "bb6-verify-"
  description = "bb6 odometer verification box: egress only, no ingress"

  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

resource "aws_instance" "verify" {
  ami                         = data.aws_ssm_parameter.ubuntu2404.value
  instance_type               = var.instance_type
  iam_instance_profile        = aws_iam_instance_profile.verify.name
  vpc_security_group_ids      = [aws_security_group.verify.id]
  associate_public_ip_address = true

  metadata_options {
    http_tokens = "required"
  }

  root_block_device {
    volume_size = 80
    volume_type = "gp3"
  }

  tags = {
    Name      = "bb6-odometer-verify"
    Project   = "bb6-holdouts"
    Ephemeral = "true"
  }
}

output "instance_id" {
  value = aws_instance.verify.id
}

output "bucket" {
  value = aws_s3_bucket.xfer.bucket
}
