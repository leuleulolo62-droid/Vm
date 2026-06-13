-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = box.Text:upper()
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'lAS7jkbkWMo49vHCSx7QkD9f'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-dJkbolkHFoz4
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, watermark = 'Y2k-dJkbolkHFoz4', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
